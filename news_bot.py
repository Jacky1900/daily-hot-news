#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
每日全球热点新闻推送：金融股票 / AI科技 / 生物医药科技 三类，各取 24 小时热度 TOP 10。
涉华报道一律过滤（见 FILTER_ALL_CHINA）；恒瑞医药（Hengrui）为白名单，强制保留并优先展示。

数据源（任一失败自动跳过，不影响整体）：
  - Hacker News (Algolia API)   有点赞数，真热度
  - Reddit top.json             有点赞数，真热度
  - Google News RSS             时效聚合
  - MarketWatch / CNBC          RSS
  - TechCrunch / Ars / MIT TR / OpenAI  RSS
  - Endpoints / BioPharma Dive / STAT   RSS

推送渠道：
  - PushPlus（微信）  每类一条 markdown 消息
  - 邮件（SMTP）      一封 HTML 完整报告

特性：
  - 纯 Python 标准库，零第三方依赖
  - 当天已推送的条目自动去重（state/pushed.json，由 Actions 自动回写仓库）
  - 标题中英双语（百度翻译，可选；不配 Key 则纯英文，不影响运行）

用法：
  python news_bot.py             # 抓取 + 推送
  python news_bot.py --dry-run   # 只抓取并打印，不推送（本地测试用）
"""

import argparse
import email
import hashlib
import html
import imaplib
import json
import os
import random
import re
import smtplib
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone, timedelta
from email.header import Header, decode_header
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import formataddr, parseaddr, parsedate_to_datetime

# ---------------- 基本配置 ----------------

UA = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json, application/rss+xml, application/xml, text/xml, */*",
    "Accept-Language": "en-US,en;q=0.9",
}
TIMEOUT = 10          # 单源超时（秒）
RETRIES = 2           # 单源重试次数
WINDOW = 24 * 3600    # 热度窗口：24 小时
TOP_N = {             # 每类取前 N 条
    "finance": 10,
    "ai": 10,
    "pharma": 10,
}
SOURCE_CAP = 4        # 同一来源最多占几条（防止单源霸榜）
REPEAT_BONUS = 8      # 同一条新闻被多个源报道，每多一个源加的分
MAX_PUSH_CHARS = 9000  # PushPlus 单条消息长度上限保护（超长会被平台拒绝）

BJT = timezone(timedelta(hours=8))  # 北京时间

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
STATE_DIR = os.path.join(BASE_DIR, "state")
PUSHED_FILE = os.path.join(STATE_DIR, "pushed.json")
TRANS_CACHE_FILE = os.path.join(STATE_DIR, "translation_cache.json")
PAUSE_FILE = os.path.join(STATE_DIR, "paused.json")

# ---------------- 邮件远程开关 ----------------
# 发一封邮件到 SMTP_USER 那个邮箱，只认【主题】，不认正文（避免误判）
# 采用"主题完全相等"匹配，所以用一个单词也安全：
#   主题 = stop  => 暂停；主题 = start => 恢复
# 主题里带别的字（如 "Stop loss triggered"）不会触发，只会精确匹配才生效
STOP_SUBJECT = "STOP"      # 主题完全等于它 => 暂停抓取
RESUME_SUBJECT = "START"   # 主题完全等于它 => 恢复抓取
IMAP_HOST = os.environ.get("IMAP_HOST", "").strip() or "imap.qq.com"
IMAP_LOOKBACK_DAYS = 30            # 只检查最近 30 天的邮件
IMAP_MAX_MAILS = 40                # 最多扫最近 40 封

CATEGORIES = {
    "finance": "金融股票",
    "ai": "AI科技",
    "pharma": "生物医药科技",
}
CAT_EMOJI = {"finance": "📈", "ai": "🤖", "pharma": "🧬"}

# ---------------- 内容过滤 ----------------

# 涉华关键词：标题或摘要命中任意一个，整条直接丢弃（不分类别，包括战争类）
# 需求来源：用户明确要求"涉华报道一律不要抓取"。想放宽时把 FILTER_ALL_CHINA 改成 False，
# 就只会过滤"涉华 + 政治敏感词"的报道，保留涉华科技/产业新闻。
FILTER_ALL_CHINA = True

CHINA_TERMS = [
    # 国家与地区
    "china", "chinese", "prc", "beijing", "shanghai", "shenzhen",
    "hong kong", "taiwan", "taiwanese", "tsmc",
    "xinjiang", "tibet", "uyghur",
    # 政治机构与人物
    "ccp", "communist party", "politburo", "xi jinping", "tiananmen",
    # 中国企业
    "huawei", "tiktok", "bytedance", "alibaba", "tencent", "baidu",
    "dji", "smic", "catl", "byd", "xiaomi", "geely", "nio",
    # 货币
    "renminbi", "yuan",
]

# FILTER_ALL_CHINA=False 时才用：涉华 + 这些词 => 才算涉华政治类
CHINA_POLITICAL_TERMS = [
    "ccp", "communist party", "politburo", "xi jinping", "tiananmen",
    "taiwan independence", "xinjiang", "tibet", "hong kong protest",
    "uyghur", "dalai lama", "falun gong", "human rights", "censorship",
    "election", "sanctions", "military", "threat", "crackdown", "protest",
]


def is_china_news(text):
    """判断是否涉华（标题 + 摘要一起看）。"""
    t = (text or "").lower()
    if not any(w in t for w in CHINA_TERMS):
        return False
    if FILTER_ALL_CHINA:
        return True
    return any(w in t for w in CHINA_POLITICAL_TERMS)


# 恒瑞医药白名单：命中即强制保留（不受涉华过滤影响），并额外加分保证进榜
HENGRUI_TERMS = ["hengrui", "恒瑞"]
HENGRUI_BONUS = 60


def is_hengrui(text):
    """是否恒瑞医药相关新闻。"""
    t = (text or "").lower()
    return any(w in t for w in HENGRUI_TERMS)

# Hacker News 查询：(关键词, 分类, 最低点赞数)
HN_QUERIES = [
    ("AI", "ai", 50),
    ("artificial intelligence", "ai", 50),
    ("stocks", "finance", 30),
    ("stock market", "finance", 30),
    ("biotech", "pharma", 20),
    ("pharmaceutical", "pharma", 20),
    ("FDA approval", "pharma", 20),
]

# Reddit 板块：(板块名, 分类)
REDDIT_SUBS = [
    ("wallstreetbets", "finance"),
    ("stocks", "finance"),
    ("investing", "finance"),
    ("artificial", "ai"),
    ("MachineLearning", "ai"),
    ("singularity", "ai"),
    ("biotech", "pharma"),
    ("pharma", "pharma"),
]

# Google News 查询：(查询词, 分类)  自动追加 when:1d
GOOGLE_NEWS_QUERIES = [
    ("stock market OR earnings OR wall street", "finance"),
    ('"artificial intelligence" OR OpenAI OR Anthropic OR Nvidia', "ai"),
    ('biotech OR pharmaceutical OR "FDA approval" OR "clinical trial"', "pharma"),
    ("Hengrui OR \"Jiangsu Hengrui\" OR \"恒瑞医药\"", "pharma"),  # 恒瑞专项
]

# 通用 RSS：(地址, 分类, 来源名)
RSS_FEEDS = [
    ("https://feeds.content.dowjones.io/public/rss/mw_topstories", "finance", "MarketWatch"),
    ("https://www.cnbc.com/id/10000664/device/rss/rss.html", "finance", "CNBC"),
    ("https://www.cnbc.com/id/20910258/device/rss/rss.html", "finance", "CNBC Markets"),
    ("https://www.cnbc.com/id/15839135/device/rss/rss.html", "finance", "CNBC Earnings"),
    ("https://techcrunch.com/feed/", "ai", "TechCrunch"),
    ("https://arstechnica.com/ai/feed/", "ai", "Ars Technica"),
    ("https://www.technologyreview.com/feed/", "ai", "MIT Tech Review"),
    ("https://openai.com/news/rss.xml", "ai", "OpenAI"),
    ("https://endpts.com/feed/", "pharma", "Endpoints News"),
    ("https://www.biopharmadive.com/feeds/news/", "pharma", "BioPharma Dive"),
    ("https://www.statnews.com/feed/", "pharma", "STAT"),
    # 战争/军事类
    ("https://www.labiotech.eu/feed/", "pharma", "Labiotech"),
]


# ---------------- 工具函数 ----------------

# 所有敏感环境变量名（公开仓库里日志对所有人可见，绝不能把它们的值打进日志）
SENSITIVE_ENV_KEYS = (
    "PUSHPLUS_TOKEN",
    "SMTP_USER",
    "SMTP_PASS",
    "MAIL_TO",
    "BAIDU_TRANS_APPID",
    "BAIDU_TRANS_SECRET",
)


def redact(text):
    """
    日志脱敏：把出现的敏感凭证值全部换成 ***。
    双重兜底：先替换完整值，再替换邮箱 @ 前面的本地部分
    （服务器报错时常只回显 "xxx123" 而不带 @qq.com，这一层专治这种情况）。
    """
    if not text:
        return text
    s = str(text)
    for key in SENSITIVE_ENV_KEYS:
        val = os.environ.get(key, "").strip()
        if len(val) < 4:
            continue
        s = s.replace(val, "***")
        if "@" in val:
            local = val.split("@", 1)[0]
            if len(local) >= 4:
                s = s.replace(local, "***")
    return s


def mask_email(addr):
    """展示用的邮箱掩码：abc123@qq.com -> ab***@qq.com"""
    if not addr or "@" not in addr:
        return "***"
    local, domain = addr.split("@", 1)
    return (local[:2] + "***@" + domain) if len(local) > 2 else "***@" + domain


def log(msg):
    """所有日志统一走脱敏，防止公开仓库 Actions 日志泄露凭证。"""
    print("[%s] %s" % (datetime.now(BJT).strftime("%H:%M:%S"), redact(msg)), flush=True)


def http_get(url, retries=RETRIES, timeout=TIMEOUT):
    """带重试的 GET，返回 bytes；失败抛异常。"""
    last = None
    for i in range(retries):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except Exception as e:  # noqa: BLE001
            last = e
            time.sleep(1)
    raise last


def http_json(url, **kw):
    return json.loads(http_get(url, **kw).decode("utf-8", "replace"))


def now_ts():
    return int(time.time())


def fresh_bonus(ts):
    """时效加分：越新鲜分越高。"""
    if not ts:
        return 0
    age = now_ts() - ts
    if age <= 3 * 3600:
        return 15
    if age <= 8 * 3600:
        return 10
    if age <= WINDOW:
        return 5
    return 0


def norm_key(title):
    """标题归一化，用于跨源去重。"""
    t = (title or "").lower()
    t = re.sub(r"https?://\S+", "", t)
    t = re.sub(r"[^a-z0-9\u4e00-\u9fff]+", " ", t)
    t = re.sub(r"\s+", " ", t).strip()
    return hashlib.md5(t.encode("utf-8")).hexdigest() if t else ""


def clean_md(text):
    """清掉会破坏 markdown 格式的字符。"""
    return re.sub(r"[`\[\]{}|*#]", "", text or "").strip()


def clean_summary(raw, max_len=200):
    """把 RSS 的 description（HTML 片段）清成纯文本摘要。"""
    if not raw:
        return ""
    t = re.sub(r"<script.*?</script>", " ", raw, flags=re.S | re.I)
    t = re.sub(r"<style.*?</style>", " ", t, flags=re.S | re.I)
    t = re.sub(r"<[^>]+>", " ", t)
    t = html.unescape(t)
    t = re.sub(r"\s+", " ", t).strip()
    if len(t) > max_len:
        t = t[:max_len].rstrip() + "…"
    return t


def fmt_age(ts):
    if not ts:
        return "时间未知"
    age = max(0, now_ts() - ts)
    if age < 3600:
        return "%d分钟前" % (age // 60)
    if age < 86400:
        return "%d小时前" % (age // 3600)
    return "%d天前" % (age // 86400)


def fmt_dt(ts):
    dt = datetime.fromtimestamp(ts, BJT) if ts else datetime.now(BJT)
    return dt.strftime("%m月%d日 %H:%M")


def rss_ts(text):
    """解析 RSS/RFC822 时间。没有时区时按 UTC 处理，避免本地环境和 Actions 算出不同结果。"""
    if not text:
        return None
    try:
        dt = parsedate_to_datetime(text)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return int(dt.timestamp())
    except Exception:  # noqa: BLE001
        return None


# ---------------- 抓取 ----------------

def fetch_hn():
    """Hacker News（Algolia）：按点赞数取 24 小时内热帖。"""
    items = []
    since = now_ts() - WINDOW
    for query, cat, min_pts in HN_QUERIES:
        try:
            nf = urllib.parse.quote("points>%d,created_at_i>%d" % (min_pts, since))
            url = (
                "https://hn.algolia.com/api/v1/search?query=%s"
                "&restrictSearchableAttributes=title&tags=story&hitsPerPage=20&numericFilters=%s"
                % (urllib.parse.quote(query), nf)
            )
            hits = http_json(url).get("hits", [])
            for h in hits:
                title = (h.get("title") or "").strip()
                if title.startswith(("Show HN:", "Ask HN:", "Tell HN:")):
                    continue
                items.append({
                    "title": title,
                    "url": h.get("url") or "https://news.ycombinator.com/item?id=%s" % h.get("objectID"),
                    "source": "Hacker News",
                    "category": cat,
                    "score": int(h.get("points") or 0),
                    "ts": int(h.get("created_at_i") or 0) or None,
                })
            log("  HN [%s] -> %d 条" % (query, len(hits)))
        except Exception as e:  # noqa: BLE001
            log("  HN [%s] 失败: %s" % (query, e))
    return items


def fetch_reddit():
    """Reddit 当日热帖（海外服务器可达；本机可能超时，失败自动跳过）。"""
    items = []
    for sub, cat in REDDIT_SUBS:
        try:
            url = "https://www.reddit.com/r/%s/top.json?t=day&limit=20&raw_json=1" % sub
            data = http_json(url, timeout=8)
            children = data.get("data", {}).get("children", [])
            for c in children:
                d = c.get("data", {})
                if d.get("stickied"):
                    continue
                items.append({
                    "title": (d.get("title") or "").strip(),
                    "url": "https://www.reddit.com" + d.get("permalink", ""),
                    "source": "r/%s" % sub,
                    "category": cat,
                    "score": int(d.get("score") or 0) + 0.5 * int(d.get("num_comments") or 0),
                    "ts": int(d.get("created_utc") or 0) or None,
                    "summary": clean_summary(d.get("selftext")),
                })
            log("  Reddit r/%s -> %d 条" % (sub, len(children)))
        except Exception as e:  # noqa: BLE001
            log("  Reddit r/%s 失败: %s" % (sub, e))
    return items


def fetch_google_news():
    """Google News RSS：时效性聚合源。"""
    items = []
    for query, cat in GOOGLE_NEWS_QUERIES:
        try:
            url = (
                "https://news.google.com/rss/search?q=%s&hl=en-US&gl=US&ceid=US:en"
                % urllib.parse.quote(query + " when:1d")
            )
            root = ET.fromstring(http_get(url, timeout=8))
            for it in root.findall(".//item")[:20]:
                title = (it.findtext("title") or "").strip()
                # Google News 标题格式："标题 - 来源"
                parts = title.rsplit(" - ", 1)
                real_title = parts[0] if len(parts) == 2 else title
                src_name = it.findtext("source") or (parts[1] if len(parts) == 2 else "Google News")
                items.append({
                    "title": real_title,
                    "url": (it.findtext("link") or "").strip(),
                    "source": src_name,
                    "category": cat,
                    "score": 40 + fresh_bonus(rss_ts(it.findtext("pubDate"))),
                    "ts": rss_ts(it.findtext("pubDate")),
                })
            log("  GoogleNews [%s] -> ok" % query[:30])
        except Exception as e:  # noqa: BLE001
            log("  GoogleNews [%s] 失败: %s" % (query[:30], e))
    return items


def fetch_rss():
    """通用 RSS 源。"""
    items = []
    for url, cat, name in RSS_FEEDS:
        try:
            root = ET.fromstring(http_get(url))
            for it in root.findall(".//item")[:15]:
                title = (it.findtext("title") or "").strip()
                if not title:
                    continue
                ts = rss_ts(it.findtext("pubDate"))
                items.append({
                    "title": title,
                    "url": (it.findtext("link") or "").strip(),
                    "source": name,
                    "category": cat,
                    "score": 40 + fresh_bonus(ts),
                    "ts": ts,
                    "summary": clean_summary(it.findtext("description")),
                })
            log("  RSS %s -> ok" % name)
        except Exception as e:  # noqa: BLE001
            log("  RSS %s 失败: %s" % (name, e))
    return items


# ---------------- 聚合排序 ----------------

def is_personal_advice(title):
    """过滤个人理财咨询类软文（MarketWatch 的 Moneyist 专栏等：问号结尾 + 第一人称）。"""
    t = (title or "").strip()
    if not t.endswith("?"):
        return False
    if re.match(r"^(My|I|We)\b", t):
        return True
    return bool(re.search(r"\bmy\b", t, re.IGNORECASE))


def is_opinion(title):
    """过滤观点评论栏。"""
    return (title or "").strip().lower().startswith(("opinion:", "editorial:", "letter:"))


def is_stale(it):
    """超过 30 小时的旧闻直接丢弃（热度窗口 24 小时 + 6 小时缓冲）。"""
    ts = it.get("ts")
    return bool(ts) and (now_ts() - ts) > (WINDOW + 6 * 3600)


def merge_and_rank(items):
    """跨源去重合并：先过滤（涉华 / 软文 / 观点 / 旧闻），再按热度排序，每类取 TOP_N。"""
    by_key = {}
    n_china = 0
    n_hengrui = 0
    for it in items:
        k = norm_key(it["title"])
        if not k or not it["title"]:
            continue
        if is_personal_advice(it["title"]) or is_opinion(it["title"]) or is_stale(it):
            continue
        text = it["title"] + " " + (it.get("summary") or "")
        hr = is_hengrui(text)
        if hr:
            n_hengrui += 1
        # 涉华报道整条丢弃；恒瑞医药是白名单，不受此限
        if not hr and is_china_news(text):
            n_china += 1
            continue
        it = dict(it)
        if hr:
            it["score"] += HENGRUI_BONUS  # 保证恒瑞新闻排进榜单
        it["key"] = k
        it["key"] = k
        if k in by_key:
            old = by_key[k]
            old["score"] += REPEAT_BONUS
            old["multi"] += 1
            # 保留分数最高来源的链接与来源名
            if it["score"] > old["base_score"]:
                old["url"] = it["url"]
                old["source"] = it["source"]
                old["base_score"] = it["score"]
            if it["ts"] and (not old["ts"] or it["ts"] < old["ts"]):
                old["ts"] = it["ts"]
            # 同一个事件，哪个源给了摘要就补上（邮件里用）
            if it.get("summary") and not old.get("summary"):
                old["summary"] = it["summary"]
        else:
            it["multi"] = 0
            it["base_score"] = it["score"]
            by_key[k] = it

    ranked = {cat: [] for cat in CATEGORIES}
    for it in by_key.values():
        cat = it.get("category")
        if cat not in ranked:
            continue
        ranked[cat].append(it)
    for cat in ranked:
        ranked[cat].sort(key=lambda x: x["score"], reverse=True)
        ranked[cat] = diversify(ranked[cat], TOP_N[cat])
    if n_china or n_hengrui:
        log("  过滤涉华报道 %d 条 | 恒瑞医药白名单保留 %d 条" % (n_china, n_hengrui))
    return ranked


def diversify(items, top_n, cap=SOURCE_CAP):
    """单来源限流：同一来源最多 cap 条，避免一个源霸榜。"""
    out, per_src = [], {}
    for it in items:
        src = it["source"]
        if per_src.get(src, 0) >= cap:
            continue
        per_src[src] = per_src.get(src, 0) + 1
        out.append(it)
        if len(out) >= top_n:
            break
    return out


# ---------------- 翻译（百度翻译，可选） ----------------

_trans_cache = None


def load_trans_cache():
    global _trans_cache
    if _trans_cache is None:
        try:
            with open(TRANS_CACHE_FILE, "r", encoding="utf-8") as f:
                _trans_cache = json.load(f)
        except Exception:  # noqa: BLE001
            _trans_cache = {}
    return _trans_cache


def save_trans_cache():
    global _trans_cache
    try:
        # 控制仓库体积：只保留最近 3000 条翻译
        if len(_trans_cache) > 3000:
            _trans_cache = dict(list(_trans_cache.items())[-3000:])
        os.makedirs(STATE_DIR, exist_ok=True)
        with open(TRANS_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(_trans_cache, f, ensure_ascii=False, indent=1)
    except Exception as e:  # noqa: BLE001
        log("翻译缓存保存失败: %s" % e)


def translate_baidu(texts, appid, secret):
    """百度翻译（需 APP ID + 密钥。注意：标准版免费额度仅 5 万字符/月）。"""
    cache = load_trans_cache()
    result = {}
    todo = [t for t in texts if t and t not in cache]

    consecutive_fail = 0
    for t in todo:
        try:
            salt = str(random.randint(10000000, 99999999))
            sign = hashlib.md5((appid + t + salt + secret).encode("utf-8")).hexdigest()
            params = urllib.parse.urlencode({
                "q": t, "from": "auto", "to": "zh",
                "appid": appid, "salt": salt, "sign": sign,
            })
            url = "https://fanyi-api.baidu.com/api/trans/vip/translate?" + params
            data = json.loads(http_get(url, timeout=15).decode("utf-8", "replace"))

            err = data.get("error_code")
            if err:
                consecutive_fail += 1
                log("  翻译失败: %s (百度错误码 %s)" % (t[:40], err))
                if consecutive_fail >= 3:
                    log("  百度翻译连续失败 3 次，停止翻译（检查 APP ID 和密钥是否配对）")
                    break
                time.sleep(1.1)
                continue

            dst = (data.get("trans_result") or [{}])[0].get("dst")
            if dst:
                cache[t] = dst
                result[t] = dst
                consecutive_fail = 0
            else:
                log("  翻译无结果: %s" % t[:40])
            time.sleep(1.1)  # 百度翻译标准版 QPS=1
        except Exception as e:  # noqa: BLE001
            consecutive_fail += 1
            log("  翻译异常: %s (%s)" % (t[:40], e))
            if consecutive_fail >= 3:
                log("  百度翻译连续异常 3 次，停止翻译")
                break

    if result:
        save_trans_cache()
    for t in texts:
        if t in cache:
            result[t] = cache[t]
    return result


def translate_google(texts):
    """
    Google 免费翻译接口（translate_a/single）：无需 Key、无需注册、不限额度。
    属非官方接口，GitHub 海外服务器可访问；国内本机可能不通。
    失败自动降级为英文标题，不影响推送。
    """
    cache = load_trans_cache()
    result = {}
    todo = [t for t in texts if t and t not in cache]
    fail = 0

    for t in todo:
        try:
            params = urllib.parse.urlencode({
                "client": "gtx", "sl": "auto", "tl": "zh-CN", "dt": "t", "q": t,
            })
            url = "https://translate.googleapis.com/translate_a/single?" + params
            raw = http_get(url, timeout=12, retries=1).decode("utf-8", "replace")
            data = json.loads(raw)
            parts = (data[0] if isinstance(data, list) and data else []) or []
            dst = "".join(
                (p[0] or "") for p in parts if isinstance(p, list) and p
            ).strip()
            if dst:
                cache[t] = dst
                result[t] = dst
                fail = 0
            else:
                fail += 1
            time.sleep(0.35)
            if fail >= 3:
                log("  Google 翻译连续失败 3 次，剩余标题保持英文")
                break
        except Exception as e:  # noqa: BLE001
            fail += 1
            log("  Google 翻译异常: %s" % e)
            if fail >= 3:
                log("  Google 翻译连续异常 3 次，剩余标题保持英文")
                break

    if result:
        save_trans_cache()
    for t in texts:
        if t in cache:
            result[t] = cache[t]
    got = sum(1 for t in texts if t in result)
    log("  Google 翻译结果：%d/%d 条有中文" % (got, len(texts)))
    if got == 0 and texts:
        log("  !! Google 接口不通，标题全部保持英文（想换百度见 README）")
    return result


def translate_titles(texts):
    """
    翻译调度：配了百度 Key 就用百度，否则用 Google 免费接口。
    全部失败时返回空 dict，标题保持英文——推送照常，不会崩。
    """
    if not texts:
        return {}
    appid = os.environ.get("BAIDU_TRANS_APPID", "").strip()
    secret = os.environ.get("BAIDU_TRANS_SECRET", "").strip()
    if appid and secret:
        log("翻译引擎：百度翻译")
        return translate_baidu(texts, appid, secret)
    log("翻译引擎：Google 免费接口（无需 Key）")
    return translate_google(texts)


# ---------------- 渲染 ----------------

def render_pushplus(ranked, trans, run_time):
    """微信推送：三类全部标题合并成一条消息，只放标题+中文，摘要细节走邮件。"""
    total = sum(len(v) for v in ranked.values())
    lines = [
        "## 🌐 每日热点 %d 条 · 全部标题" % total,
        "> %s 更新 · 24小时全球热度榜 · 摘要详见邮件" % run_time,
        "",
    ]
    for cat, cn in CATEGORIES.items():
        items = ranked.get(cat) or []
        if not items:
            continue
        lines.append("### %s %s · %d条" % (CAT_EMOJI.get(cat, ""), cn, len(items)))
        for i, it in enumerate(items, 1):
            title = clean_md(it["title"])
            zh = trans.get(it["title"])
            lines.append("%d. **[%s](%s)**" % (i, title, it["url"]))
            if zh:
                lines.append("   %s" % clean_md(zh))
        lines.append("")

    text = "\n".join(lines)
    if len(text) > MAX_PUSH_CHARS:
        text = text[:MAX_PUSH_CHARS] + "\n\n（内容超长已截断，完整版见邮件）"
    return text


def render_email_html(ranked, run_time):
    """邮件：保持英文原文（标题 + 摘要），中文靠 QQ 邮箱自带的"翻译邮件"功能。"""
    parts = [
        "<html><body style='margin:0;padding:24px;background:#f2f3f5;'>",
        "<div style='max-width:760px;margin:0 auto;background:#ffffff;border-radius:10px;padding:28px;font-family:Arial,\"PingFang SC\",\"Microsoft YaHei\",sans-serif;'>",
        "<h2 style='margin:0 0 4px;'>🌐 每日全球热点 · %s</h2>" % run_time,
        "<p style='color:#888;margin:0 0 24px;'>金融股票 / AI科技 / 生物医药科技 · 过去 24 小时热度 TOP 10 · 中文请用邮箱自带的翻译功能</p>",
    ]
    for cat, cn in CATEGORIES.items():
        items = ranked.get(cat) or []
        if not items:
            continue
        parts.append(
            "<h3 style='border-left:4px solid #d43f3a;padding-left:8px;margin:24px 0 12px;'>%s %s</h3>"
            % (CAT_EMOJI.get(cat, ""), cn)
        )
        parts.append("<table style='width:100%;border-collapse:collapse;font-size:14px;'>")
        for i, it in enumerate(items, 1):
            summary = it.get("summary") or ""
            sum_html = ""
            if summary:
                sum_html = (
                    "<div style='color:#555;font-size:13px;margin-top:8px;line-height:1.55;'>%s</div>"
                    % html.escape(summary)
                )
            meta = "%s · %s" % (html.escape(it["source"]), fmt_age(it["ts"]))
            if it.get("multi"):
                meta += " · %d家报道" % (it["multi"] + 1)
            if it.get("base_score", 0) >= 100:
                meta += " · 热度%d" % int(it["base_score"])
            parts.append(
                "<tr><td style='padding:12px 4px;border-bottom:1px solid #eee;vertical-align:top;width:28px;color:#999;'>%d</td>"
                "<td style='padding:12px 4px;border-bottom:1px solid #eee;'>"
                "<a href='%s' style='color:#1a0dab;text-decoration:none;font-weight:bold;font-size:15px;'>%s</a>%s"
                "<div style='color:#aaa;font-size:12px;margin-top:6px;'>%s</div></td></tr>"
                % (i, html.escape(it["url"]), html.escape(it["title"]), sum_html, meta)
            )
        parts.append("</table>")
    parts.append(
        "<p style='color:#bbb;font-size:12px;margin-top:28px;'>由 GitHub Actions 自动生成 · 数据来源：Hacker News / Reddit / Google News / MarketWatch / CNBC / TechCrunch / Endpoints / STAT 等</p>"
        "</div></body></html>"
    )
    return "".join(parts)


# ---------------- 推送 ----------------

def send_pushplus(token, title, content):
    """PushPlus 微信推送，成功返回 True（网络异常重试 1 次，业务错误不重试）。"""
    body = json.dumps({
        "token": token,
        "title": title,
        "content": content,
        "template": "markdown",
    }).encode("utf-8")

    for attempt in range(2):
        req = urllib.request.Request(
            "https://www.pushplus.plus/send", data=body,
            headers={"Content-Type": "application/json"},
        )
        try:
            with urllib.request.urlopen(req, timeout=20) as r:
                resp = json.loads(r.read().decode("utf-8", "replace"))
            if resp.get("code") == 200:
                log("PushPlus 推送成功: %s" % title)
                return True
            # 业务错误（token 错、额度用完等）重试也没用，直接返回
            log("PushPlus 推送失败: %s (%s)" % (title, resp.get("msg")))
            return False
        except Exception as e:  # noqa: BLE001
            log("PushPlus 推送异常（第%d次）: %s (%s)" % (attempt + 1, title, e))
            if attempt == 0:
                time.sleep(2)
    return False


def send_email(subject, html_body):
    """SMTP 邮件推送（QQ/163 用 465 SSL；Gmail 用 587 STARTTLS）。"""
    host = os.environ.get("SMTP_HOST", "").strip()
    port_raw = os.environ.get("SMTP_PORT", "").strip()
    try:
        port = int(port_raw) if port_raw else 465
    except ValueError:
        log("SMTP_PORT 填的不是数字（%s），按 465 处理" % port_raw)
        port = 465
    user = os.environ.get("SMTP_USER", "").strip()
    passwd = os.environ.get("SMTP_PASS", "").strip()
    mail_to = os.environ.get("MAIL_TO", "").strip()
    if not (host and user and passwd and mail_to):
        log("SMTP 未配置完整，跳过邮件推送")
        return False

    msg = MIMEMultipart("alternative")
    msg["Subject"] = Header(subject, "utf-8")
    msg["From"] = formataddr((str(Header("全球热点日报", "utf-8")), user))
    msg["To"] = mail_to
    msg.attach(MIMEText("请使用支持 HTML 的邮件客户端查看本邮件。", "plain", "utf-8"))
    msg.attach(MIMEText(html_body, "html", "utf-8"))

    try:
        if port == 465:
            server = smtplib.SMTP_SSL(host, port, timeout=30)
        else:
            server = smtplib.SMTP(host, port, timeout=30)
            server.starttls()
        with server:
            server.login(user, passwd)
            server.sendmail(user, [mail_to], msg.as_string())
        log("邮件推送成功 -> %s" % mask_email(mail_to))
        return True
    except Exception as e:  # noqa: BLE001
        log("邮件推送失败: %s" % e)
        return False


# ---------------- 邮件远程开关（STOP / START） ----------------

def decode_mime_header(raw):
    """解码邮件主题（可能含 UTF-8/GBK 编码段）。"""
    if not raw:
        return ""
    out = []
    for text, enc in decode_header(raw):
        if isinstance(text, bytes):
            out.append(text.decode(enc or "utf-8", "replace"))
        else:
            out.append(text)
    return "".join(out).strip()


def normalize_subject(subject):
    """
    归一化邮件主题用于精确匹配口令：
    去掉 Re:/Fwd:/回复:/转发: 这类前缀（最多 3 层），去空白，转大写。
    这样"回复 stop"变成"STOP"仍然有效，而"Stop loss triggered"不会误命中。
    """
    s = (subject or "").strip()
    for _ in range(3):
        m = re.match(r"^(re|fwd|fw|回复|转发|答复)\s*[:：]\s*", s, re.I)
        if not m:
            break
        s = s[m.end():].strip()
    return s.upper()


def check_email_command():
    """
    通过 IMAP 只读检查最近的邮件主题，找停止/恢复口令。
    返回 "stop" / "resume" / None。任何失败都返回 None，绝不影响正常推送。
    只读模式：不标记已读、不移动、不删除任何邮件。
    """
    user = os.environ.get("SMTP_USER", "").strip()
    passwd = os.environ.get("SMTP_PASS", "").strip()
    if not user or not passwd:
        return None

    conn = None
    try:
        conn = imaplib.IMAP4_SSL(IMAP_HOST, 993, timeout=20)
        conn.login(user, passwd)
        conn.select("INBOX", readonly=True)  # 只读，不改动邮箱

        since = (datetime.now(BJT) - timedelta(days=IMAP_LOOKBACK_DAYS)).strftime("%d-%b-%Y")
        status, data = conn.search(None, "SINCE", since)
        if status != "OK" or not data or not data[0]:
            return None

        ids = data[0].split()[-IMAP_MAX_MAILS:]
        # 从最新往前扫，遇到第一条口令邮件就按它执行
        for mid in reversed(ids):
            try:
                st, msg_data = conn.fetch(mid, "(BODY.PEEK[HEADER])")
                if st != "OK" or not msg_data or not msg_data[0]:
                    continue
                msg = email.message_from_bytes(msg_data[0][1])
                subject = decode_mime_header(msg.get("Subject"))
                sender = parseaddr(msg.get("From", "") or "")[1].lower().strip()
            except Exception:  # noqa: BLE001
                continue

            norm = normalize_subject(subject)
            if norm not in (STOP_SUBJECT, RESUME_SUBJECT):
                continue
            # 只接受自己邮箱发来的指令：防止任何人（知道口令是 stop）发一封邮件就把你的推送停掉
            if sender and user.lower() not in sender:
                log("  邮箱指令：忽略非本人发来的指令（发件人 %s）" % mask_email(sender))
                continue

            if norm == STOP_SUBJECT:
                log("  邮箱指令：检测到停止指令（主题「%s」）" % subject[:40])
                return "stop"
            log("  邮箱指令：检测到恢复指令（主题「%s」）" % subject[:40])
            return "resume"
        log("  邮箱指令：最近 %d 封里没有 stop/start（中文字或别的字不算），继续正常抓取"
            % len(ids))
        return None
    except Exception as e:  # noqa: BLE001
        log("  检查邮箱指令失败（不影响推送）: %s" % e)
        return None
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:  # noqa: BLE001
                pass
            try:
                conn.logout()
            except Exception:  # noqa: BLE001
                pass


def load_paused():
    try:
        with open(PAUSE_FILE, "r", encoding="utf-8") as f:
            return bool(json.load(f).get("paused"))
    except Exception:  # noqa: BLE001
        return False


def save_paused(flag):
    try:
        os.makedirs(STATE_DIR, exist_ok=True)
        with open(PAUSE_FILE, "w", encoding="utf-8") as f:
            json.dump({
                "paused": bool(flag),
                "since": datetime.now(BJT).strftime("%Y-%m-%d %H:%M"),
            }, f, ensure_ascii=False)
    except Exception as e:  # noqa: BLE001
        log("暂停状态保存失败: %s" % e)


def notify_paused(token, run_time, stopped):
    """暂停/恢复时发一条简短微信通知，让你知道指令生效了。"""
    if not token:
        return
    if stopped:
        title = "新闻脚本已暂停"
        text = (
            "## ⏸ 脚本已暂停\n> %s\n\n收到停止指令（主题：stop），之后不再抓取新闻。\n\n"
            "想恢复：发邮件，**主题**只写 `start`" % run_time
        )
    else:
        title = "新闻脚本已恢复"
        text = "## ▶️ 脚本已恢复\n> %s\n\n收到恢复指令（主题：start），下次定时任务正常抓取。" % run_time
    send_pushplus(token, title, text)


# ---------------- 状态（当天已推送去重） ----------------

def load_pushed():
    today = datetime.now(BJT).strftime("%Y-%m-%d")
    try:
        with open(PUSHED_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if data.get("date") == today:
            return set(data.get("keys", []))
    except Exception:  # noqa: BLE001
        pass
    return set()


def save_pushed(keys):
    try:
        os.makedirs(STATE_DIR, exist_ok=True)
        with open(PUSHED_FILE, "w", encoding="utf-8") as f:
            json.dump({
                "date": datetime.now(BJT).strftime("%Y-%m-%d"),
                "keys": sorted(keys),
            }, f, ensure_ascii=False)
    except Exception as e:  # noqa: BLE001
        log("推送状态保存失败: %s" % e)


# ---------------- 主流程 ----------------

def main():
    parser = argparse.ArgumentParser(description="每日全球热点新闻抓取与推送")
    parser.add_argument("--dry-run", action="store_true", help="只抓取和打印，不推送")
    parser.add_argument("--skip-mail-command", action="store_true", help="跳过邮箱停止/恢复指令检查")
    args = parser.parse_args()

    run_time = datetime.now(BJT).strftime("%m月%d日 %H:%M")

    # ---- 先看邮箱里有没有停止/恢复指令（dry-run 不检查，方便本地调试）----
    if not args.dry_run and not args.skip_mail_command:
        cmd = check_email_command()
        token = os.environ.get("PUSHPLUS_TOKEN", "").strip()
        if cmd == "stop":
            save_paused(True)
            log("已暂停：收到停止指令（主题：%s）。之后不再抓取，恢复请发主题为 %s 的邮件"
                % (STOP_SUBJECT, RESUME_SUBJECT))
            notify_paused(token, run_time, True)
            return
        if cmd == "resume":
            save_paused(False)
            log("已恢复：收到恢复指令（主题：%s）" % RESUME_SUBJECT)
            notify_paused(token, run_time, False)
        elif load_paused():
            log("脚本处于暂停状态，本次跳过（恢复请发主题为 %s 的邮件）" % RESUME_SUBJECT)
            return

    log("开始抓取（金融股票 / AI科技 / 生物医药科技，24小时热度窗口）")

    items = []
    for fn in (fetch_hn, fetch_reddit, fetch_google_news, fetch_rss):
        try:
            items.extend(fn())
        except Exception as e:  # noqa: BLE001
            log("%s 整体失败: %s" % (fn.__name__, e))
    log("共抓取 %d 条原始条目" % len(items))

    if not items:
        log("一条都没抓到，终止（网络问题？）")
        sys.exit(1)

    ranked = merge_and_rank(items)
    for cat in CATEGORIES:
        log("  %s：合并去重后 %d 条候选" % (CATEGORIES[cat], len(ranked[cat])))

    # 当天已推送去重
    pushed_keys = load_pushed()
    if pushed_keys:
        for cat in ranked:
            before = len(ranked[cat])
            ranked[cat] = [x for x in ranked[cat] if x["key"] not in pushed_keys]
            skipped = before - len(ranked[cat])
            if skipped:
                log("  %s：跳过今天已推送的 %d 条" % (CATEGORIES[cat], skipped))

    # 只翻译微信要用的标题；邮件保持英文原文（靠 QQ 邮箱自带的"翻译邮件"功能看中文）
    all_titles = []
    for cat in ranked:
        for it in ranked[cat]:
            if it["title"] not in all_titles:
                all_titles.append(it["title"])
    trans = translate_titles(all_titles)

    # dry-run：打印结果（同样走脱敏，避免输出被贴到 issue/聊天时意外带出凭证）
    if args.dry_run:
        for cat, cn in CATEGORIES.items():
            print(redact("\n" + "=" * 60))
            print(redact("%s %s TOP %d" % (CAT_EMOJI[cat], cn, len(ranked[cat]))))
            print(redact("=" * 60))
            for i, it in enumerate(ranked[cat], 1):
                print(redact("%2d. %s" % (i, it["title"])))
                zh = trans.get(it["title"])
                if zh:
                    print(redact("    → %s" % zh))
                print(redact("    [%s | %s | 热度%.0f%s] %s" % (
                    it["source"], fmt_age(it["ts"]), it["score"],
                    " | %d家报道" % (it["multi"] + 1) if it.get("multi") else "",
                    it["url"],
                )))
                sm = it.get("summary") or ""
                if sm:
                    print(redact("    ↳ %s" % (sm[:90] + ("…" if len(sm) > 90 else ""))))
        print(redact("\n[dry-run] 不推送。配置 Key 后去掉 --dry-run 即为正式运行。"))
        return

    # 正式推送：微信一条（全部标题，速览），邮件一封（含摘要，详读）
    pushplus_token = os.environ.get("PUSHPLUS_TOKEN", "").strip()
    ok_any = False
    total_items = sum(len(v) for v in ranked.values())

    if pushplus_token:
        if total_items:
            content = render_pushplus(ranked, trans, run_time)
            title = "🌐 每日热点 %d 条 · 金融/AI/生物医药 · %s" % (total_items, run_time)
            if send_pushplus(pushplus_token, title, content):
                ok_any = True
                for cat in ranked:
                    for it in ranked[cat]:
                        pushed_keys.add(it["key"])
    else:
        log("未配置 PUSHPLUS_TOKEN，跳过微信推送")

    total = sum(len(v) for v in ranked.values())
    if total:
        subject = "【每日热点】金融/AI/生物医药 · %s" % run_time
        if send_email(subject, render_email_html(ranked, run_time)):
            ok_any = True
            # 邮件里已经包含了这三类的全部条目，必须一并记入"已推送"，
            # 否则只配邮件不配微信时，同一天三次会重复推送同样的新闻。
            for cat in ranked:
                for it in ranked[cat]:
                    pushed_keys.add(it["key"])
    else:
        log("三类都没有新内容（今天已全部推送过），不发送")

    save_pushed(pushed_keys)
    if not ok_any:
        log("没有任何渠道推送成功，请检查配置（README 第 3 步）")
        sys.exit(2)


if __name__ == "__main__":
    main()
