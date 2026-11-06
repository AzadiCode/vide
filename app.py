# -*- coding: utf-8 -*-
"""
Reel Maker — ربات ساخت ریلز اسلایدی با ویس گوینده
Stack (مثل app-6): Flask + MongoDB(pymongo / mongomock) + وب‌هوک تلگرام
- کاربر اسلایدها (عکس) رو می‌فرسته، بعد یه ویس کامل از گوینده
- ویس با ffmpeg silencedetect روی مکث‌ها بین اسلایدها تقسیم می‌شه (یا مساوی)، با دکمه قابل تنظیمه
- تقسیم مکث‌محورِ حرفه‌ای‌تر: آستانه‌ی سکوت خودکار از روی بلندی صدای خود ویس، انتخاب برش‌ها با DP (مکث‌های قوی + طول متعادل)
  و گذاشتن برش درست قبل از شروع جمله‌ی بعدی (بدون هیچ API یا سرویس بیرونی)
- انیمیشن ساده و حرفه‌ای: هر اسلاید تمام‌صفحه (بدون بلور، بدون کارت و کادر، بدون نوار بالا)، زوم خیلی نرم با شتاب ease،
  و کراس‌فید کوتاه بین اسلایدها که وسط نقطه‌ی برشِ صدا می‌افته. کل ویدیو تو یه پاس ffmpeg ساخته می‌شه. اگه ffmpeg xfade نداشت یا خطا داد، خودکار برش مستقیم (FX=lite)
- خروجی: ویدیوی ۹:۱۶ تمام‌صفحه با زوم نرم، کراس‌فید بین اسلایدها و صدای نرمال‌شده
- ساخت ویدیو در یه صف تک‌نفره (مناسب پلن رایگان Render: رم کم / CPU ضعیف)
اجرا: gunicorn app:app -w 1 --threads 4 -t 120   (حتما یک worker، چون صف داخل حافظه‌ست)
"""
import os, re, time, hashlib, logging, shutil, subprocess, tempfile, threading
from collections import deque
from datetime import datetime, timezone, timedelta

import requests
from flask import Flask, request
from pymongo import MongoClient
from pymongo.errors import DuplicateKeyError

# ───────────────────────── تنظیمات (Environment) ─────────────────────────
BOT_TOKEN   = os.environ["BOT_TOKEN"]
BASE_URL    = os.environ["BASE_URL"].rstrip("/")            # مثلا https://yourapp.onrender.com
MONGO_URI   = os.environ.get("MONGO_URI", "").strip()       # خالی = حافظه‌ی موقت (ذخیره نمی‌شه)
DAILY_LIMIT = int(os.environ.get("DAILY_LIMIT", "5"))       # تعداد ویدیو در روز برای هر کاربر
ADMIN_IDS   = {int(x) for x in os.environ.get("ADMIN_IDS", "").replace(" ", "").split(",") if x.isdigit()}
MAX_SLIDES  = int(os.environ.get("MAX_SLIDES", "8"))
MAX_AUDIO   = int(os.environ.get("MAX_AUDIO", "90"))        # حداکثر طول ویس (ثانیه)
VIDEO_W     = int(os.environ.get("VIDEO_W", "720"))
VIDEO_H     = int(os.environ.get("VIDEO_H", "1280"))
FPS         = int(os.environ.get("FPS", "25"))
PRESET      = os.environ.get("X264_PRESET", "ultrafast")
CRF         = int(os.environ.get("CRF", "24"))
SIL_DB      = os.environ.get("SIL_DB", "auto")              # آستانه‌ی سکوت؛ auto = از روی بلندی خود ویس حساب می‌شه
SIL_MIN     = float(os.environ.get("SIL_MIN", "0.18"))      # حداقل طول مکث (ثانیه)؛ مکث‌های کوتاه هم دیده می‌شن، قدرتشون در DP سنجیده می‌شه
DEBUG       = os.environ.get("DEBUG", "") == "1"            # علت دقیق خطا رو برای کاربر نشون می‌ده
FX_MODE     = os.environ.get("FX", "pro").strip().lower()   # pro = زوم نرم + کراس‌فید | lite = زوم نرم + برش مستقیم (بدون کراس‌فید)
TRANS_SEC   = float(os.environ.get("TRANS_SEC", "0.30"))    # طول کراس‌فید بین اسلایدها (ثانیه)
ZOOM_AMT    = float(os.environ.get("ZOOM_AMT", "0.07"))     # مقدار زوم هر اسلاید (۰.۰۷ = ۷٪)؛ هرچی کمتر، آروم‌تر و کم‌برش‌تر
ZOOM_CANVAS = float(os.environ.get("ZOOM_CANVAS", "3"))     # ترکیب زوم روی بوم چند برابر بزرگ‌تر؛ بیشتر = نرم‌تر (و کمی کندتر)
FX_BUDGET   = int(os.environ.get("FX_BUDGET", "480"))       # بیشترین زمان مجاز ساخت ویدیو (ثانیه)؛ بیشتر شد، خودکار نسخه‌ی ساده ساخته می‌شه
SUB_FONT    = os.environ.get("SUB_FONT", "").strip()        # مسیر فونت فارسی زیرنویس (ttf/otf)؛ خالی = خودکار از کنار app.py یا فونت‌های سیستم
SUB_SIZE    = float(os.environ.get("SUB_SIZE", "0.064"))    # اندازه‌ی متن زیرنویس نسبت به عرض ویدیو
SUB_BOTTOM  = float(os.environ.get("SUB_BOTTOM", "0.17"))   # فاصله‌ی زیرنویس از پایین (نسبت به ارتفاع)؛ بالاتر از منوی ریلز
SUB_MAX     = int(os.environ.get("SUB_MAX", "280"))         # حداکثر تعداد حرف زیرنویس هر اسلاید
MIN_SEG     = 1.0    # حداقل طول هر اسلاید در تقسیم خودکار
MIN_ADJ     = 0.5    # حداقل طول هر اسلاید موقع تنظیم دستی
BUSY        = ("analyzing", "queued", "rendering")

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("reelbot")

app = Flask(__name__)
if MONGO_URI:
    db = MongoClient(MONGO_URI, serverSelectionTimeoutMS=8000).get_database("reelbot")
else:
    import mongomock
    db = mongomock.MongoClient().get_database("reelbot")
    log.warning("MONGO_URI تنظیم نشده؛ از حافظه‌ی موقت استفاده می‌شه و با هر ری‌استارت همه‌چی پاک می‌شه")
db.sessions.create_index("t")

HOOK_SECRET = hashlib.sha256(("reel" + BOT_TOKEN).encode()).hexdigest()[:32]
# صف‌ها deque ساده‌ان و ترد با polling بررسیشون می‌کنه (نه Queue استاندارد)؛ چون Condition داخل Queue بعد از fork گانیکورن
# یه waiter مرده نگه می‌داره و ترد جدید رو هیچ‌وقت بیدار نمی‌کنه
jobs = deque()     # صف رندر ویدیو
ajobs = deque()    # صف تحلیل ویس (جدا از رندر تا پشت رندر کند گیر نکنه)
state_lock = threading.Lock()
busy_now = {"v": False}


def find_ffmpeg():
    p = shutil.which("ffmpeg")
    if p:
        return p
    import imageio_ffmpeg  # باینری ffmpeg همراه پکیج (برای رندر بدون داکر)
    return imageio_ffmpeg.get_ffmpeg_exe()


FFMPEG = find_ffmpeg()
THREADS = {}
try:
    FFVER = subprocess.run([FFMPEG, "-version"], capture_output=True, text=True, timeout=20,
                           stdin=subprocess.DEVNULL).stdout.splitlines()[0]
except Exception as _e:
    FFVER = f"ERROR: {_e}"
log.info("ffmpeg: %s -> %s", FFMPEG, FFVER)


def _has_filter(name):
    try:
        out = subprocess.run([FFMPEG, "-hide_banner", "-filters"], capture_output=True, text=True, timeout=20,
                             stdin=subprocess.DEVNULL).stdout
        return re.search(rf"\s{name}\s", out) is not None
    except Exception:
        return False


FX_OK = FX_MODE != "lite" and _has_filter("xfade")
log.info("fx: mode=%s xfade=%s", FX_MODE, FX_OK)


# ───────────────────────── زیرنویس (ASS + libass؛ شکل‌دهی و راست‌به‌چپ فارسی درست) ─────────────────────────
def find_sub_font():
    cands = [SUB_FONT] if SUB_FONT else []
    here = os.path.dirname(os.path.abspath(__file__))
    local = []
    for d in (here, os.path.join(here, "fonts")):
        try:
            local += [os.path.join(d, x) for x in os.listdir(d) if x.lower().endswith((".ttf", ".otf"))]
        except OSError:
            pass
    local.sort(key=lambda p: (("vazir" not in p.lower()), ("bold" not in p.lower()), p))
    cands += local
    cands += ["/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", "/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
              "/usr/share/fonts/truetype/noto/NotoSansArabic-Bold.ttf", "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf",
              "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"]
    return next((c for c in cands if os.path.isfile(c)), None)


def font_family(path):
    """اسم خانواده‌ی فونت از جدول name فایل ttf/otf (libass با همین اسم فونت رو پیدا می‌کنه)"""
    import struct
    try:
        with open(path, "rb") as f:
            d = f.read()
        num = struct.unpack(">H", d[4:6])[0]
        for k in range(num):
            tag, _, off, ln = struct.unpack(">4sIII", d[12 + 16 * k:28 + 16 * k])
            if tag == b"name":
                _, cnt, so = struct.unpack(">HHH", d[off:off + 6])
                best = None
                for j in range(cnt):
                    pid, eid, lid, nid, nl, no = struct.unpack(">6H", d[off + 6 + 12 * j:off + 18 + 12 * j])
                    if nid != 1:
                        continue
                    raw = d[off + so + no: off + so + no + nl]
                    txt = raw.decode("utf-16-be" if pid in (0, 3) else "latin-1", "ignore").strip()
                    if txt and (best is None or (pid == 3 and lid == 0x409)):
                        best = txt
                return best
    except Exception:
        pass
    return None


def _fesc(p):
    return p.replace("\\", "/").replace("'", "\\'").replace(":", "\\:")


SUB_PATH = find_sub_font()
SUB_FAMILY = (font_family(SUB_PATH) or os.path.splitext(os.path.basename(SUB_PATH))[0]) if SUB_PATH else None
SUB_DIR = None
if SUB_PATH:
    try:
        SUB_DIR = tempfile.mkdtemp(prefix="subfont_")
        shutil.copy(SUB_PATH, SUB_DIR)      # فقط همین یه فونت تو پوشه‌ی فونت libass؛ اسکن سریع و بدون سروکله‌زدن با فونت‌های سیستم
    except Exception as _e:
        log.warning("subtitle font copy failed: %s", _e)
        SUB_DIR = None

_SEP = re.compile(r"\s*[-‐‑‒–—―−]+\s*")


def parse_subs(text):
    """متن یه پیام → لیست زیرنویس اسلایدها؛ جداکننده = خطی که فقط خط‌تیره داره"""
    parts, cur = [], []
    for line in text.replace("\r", "").split("\n"):
        if _SEP.fullmatch(line):
            parts.append("\n".join(cur).strip())
            cur = []
        else:
            cur.append(line.strip())
    parts.append("\n".join(cur).strip())
    return parts


def _ass_time(t):
    t = max(t, 0.0)
    return f"{int(t // 3600)}:{int(t % 3600 // 60):02d}:{t % 60:05.2f}"


def write_ass(path, subs, cumf):
    """subs[i] = متن اسلاید i؛ cumf = فریم تجمعی مرز اسلایدها. متن با فید و یه حرکت کوتاه به بالا میاد؛ قبل و بعد از کراس‌فید نمی‌مونه"""
    W, H = VIDEO_W, VIDEO_H
    base = round(W * SUB_SIZE)
    ev = []
    for i, raw in enumerate(subs):
        t = (raw or "").strip()
        if not t:
            continue
        a, b = cumf[i] / FPS, cumf[i + 1] / FPS
        st = 0.2 if i == 0 else a + 0.18
        en = b - 0.1 if i == len(subs) - 1 else b - 0.2
        if en - st < 0.5:
            st, en = a, b
        k = len(t.replace("\n", ""))
        size = round(base * (1.0 if k <= 90 else 0.9 if k <= 160 else 0.8 if k <= 240 else 0.7))
        t = t.replace("\\", "/").replace("{", "(").replace("}", ")")
        t = "\\N".join(x.strip() for x in t.split("\n") if x.strip())
        y = H - round(H * SUB_BOTTOM)
        ev.append(f"Dialogue: 0,{_ass_time(st)},{_ass_time(en)},Sub,,0,0,0,,"
                  f"{{\\fs{size}\\fad(250,250)\\an2\\move({W // 2},{y + 24},{W // 2},{y},0,300)}}{t}")
    head = (f"[Script Info]\nScriptType: v4.00+\nPlayResX: {W}\nPlayResY: {H}\nWrapStyle: 0\nScaledBorderAndShadow: yes\n\n"
            "[V4+ Styles]\nFormat: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, BackColour, Bold, Italic, "
            "Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding\n"
            f"Style: Sub,{SUB_FAMILY},{base},&H00FFFFFF,&H00FFFFFF,&H00000000,&H78000000,-1,0,0,0,100,100,0,0,1,3.2,1.2,2,{round(W * 0.08)},{round(W * 0.08)},{round(H * SUB_BOTTOM)},1\n\n"
            "[Events]\nFormat: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text\n")
    with open(path, "w", encoding="utf-8") as f:
        f.write(head + "\n".join(ev) + "\n")


def ass_filter(path):
    return f"ass=filename={_fesc(path)}:fontsdir={_fesc(SUB_DIR)}"


def _subs_selftest():
    if not (SUB_PATH and SUB_DIR and _has_filter("ass")):
        return False
    d = tempfile.mkdtemp(prefix="subtest_")
    try:
        p = os.path.join(d, "t.ass")
        write_ass(p, ["تست زیرنویس"], [0, 5])
        r = subprocess.run([FFMPEG, "-y", "-hide_banner", "-loglevel", "error", "-f", "lavfi", "-i", "color=c=black:s=160x284:r=5:d=1",
                            "-vf", ass_filter(p), "-frames:v", "2", "-f", "null", "-"], capture_output=True, text=True,
                           timeout=30, stdin=subprocess.DEVNULL)
        if r.returncode != 0:
            log.warning("subtitle selftest failed: %s", r.stderr[-300:])
        return r.returncode == 0
    except Exception as _e:
        log.warning("subtitle selftest error: %s", _e)
        return False
    finally:
        shutil.rmtree(d, ignore_errors=True)


SUBS_OK = _subs_selftest()
log.info("subtitles: ok=%s font=%s family=%s", SUBS_OK, SUB_PATH, SUB_FAMILY)


# ───────────────────────── ابزارهای تلگرام ─────────────────────────
def tg(method, **data):
    try:
        r = requests.post(f"https://api.telegram.org/bot{BOT_TOKEN}/{method}", json=data, timeout=15)
        return r.json()
    except Exception as e:
        log.warning("tg %s failed: %s", method, e)
        return {"ok": False, "description": str(e)}


def tg_upload(method, data, files):
    try:
        r = requests.post(f"https://api.telegram.org/bot{BOT_TOKEN}/{method}", data=data, files=files, timeout=300)
        return r.json()
    except Exception as e:
        log.warning("tg upload %s failed: %s", method, e)
        return {"ok": False, "description": str(e)}


def tg_download(file_id, dest_base, deadline=45, tries=3):
    """فایل رو دانلود می‌کنه؛ هر تلاش سقف زمان کلی داره و اگه گیر کرد دوباره تلاش می‌کنه (قبلاً می‌تونست بی‌صدا تا ابد گیر کنه)"""
    last = None
    for k in range(1, tries + 1):
        t0 = time.time()
        try:
            r = tg("getFile", file_id=file_id)
            if not r.get("ok"):
                raise RuntimeError("getFile: " + str(r.get("description")))
            path = r["result"]["file_path"]
            dest = dest_base + (os.path.splitext(path)[1] or "")
            with requests.get(f"https://api.telegram.org/file/bot{BOT_TOKEN}/{path}", stream=True, timeout=(10, 15)) as resp:
                resp.raise_for_status()
                with open(dest, "wb") as f:
                    for ch in resp.iter_content(65536):
                        if time.time() - t0 > deadline:
                            raise TimeoutError(f"download slower than {deadline}s")
                        f.write(ch)
            log.info("download ok %s (try %d, %.1fs, %d bytes)", os.path.basename(dest), k, time.time() - t0, os.path.getsize(dest))
            return dest
        except Exception as e:
            last = e
            log.warning("download try %d/%d failed after %.1fs: %s", k, tries, time.time() - t0, e)
            time.sleep(1.5)
    raise RuntimeError(f"download failed: {last}")


def say(chat, text, markup=None):
    return tg("sendMessage", chat_id=chat, text=text, **({"reply_markup": markup} if markup else {}))


def edit(chat, mid, text, markup=None):
    return tg("editMessageText", chat_id=chat, message_id=mid, text=text,
              **({"reply_markup": markup} if markup else {}))


def now():
    return datetime.now(timezone.utc)


def kb(rows):
    return {"inline_keyboard": rows}


def stage(uid, name):
    """مرحله‌ی فعلی کار رو ثبت می‌کنه تا اگه گیر کرد معلوم باشه کجاست"""
    log.info("stage uid=%s %s", uid, name)
    db.sessions.update_one({"_id": uid}, {"$set": {"stage": name, "stage_t": time.time()}})


def watchdog(uid, chat):
    s = db.sessions.find_one({"_id": uid})
    if not s or s.get("step") != "analyzing":
        return
    th = THREADS.get("analyze")
    since = f"{time.time() - s['stage_t']:.0f} ثانیه پیش" if s.get("stage_t") else "-"
    say(chat, "⚠️ تحلیل ویس طولانی شد.\n"
              f"مرحله: {s.get('stage', 'هنوز شروع نشده')} ({since})\n"
              f"ترد تحلیل زنده: {'بله' if th and th.is_alive() else 'نه'} • صف: {len(ajobs)}\n"
              f"ffmpeg: {FFVER}")


# ───────────────────────── سهمیه ─────────────────────────
def quota_key(uid):
    return f"{uid}:{now():%Y-%m-%d}"


def quota_take(uid):
    if uid in ADMIN_IDS:
        return True
    try:
        db.usage.find_one_and_update(
            {"_id": quota_key(uid), "n": {"$lt": DAILY_LIMIT}},
            {"$inc": {"n": 1}}, upsert=True)
        return True
    except DuplicateKeyError:
        return False


def quota_refund(uid):
    if uid not in ADMIN_IDS:
        db.usage.update_one({"_id": quota_key(uid)}, {"$inc": {"n": -1}})


# ───────────────────────── ffmpeg ─────────────────────────
def run(cmd, timeout=300):
    p = subprocess.run(cmd, capture_output=True, encoding="utf-8", errors="replace", timeout=timeout,
                       stdin=subprocess.DEVNULL)
    if p.returncode != 0:
        raise RuntimeError((p.stderr or "")[-700:])
    return p.stderr or ""


def parse_silence(err):
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", err)
    dur = int(m[1]) * 3600 + int(m[2]) * 60 + float(m[3]) if m else 0.0
    starts = [max(0.0, float(x)) for x in re.findall(r"silence_start:\s*(-?[\d.]+)", err)]
    ends = [float(a) for a, _ in re.findall(r"silence_end:\s*([\d.]+)\s*\|\s*silence_duration:\s*([\d.]+)", err)]
    out = []
    for i, st in enumerate(starts):
        en = ends[i] if i < len(ends) else dur
        out.append((st, en, en - st))
    return dur, out


def cuts_equal(n, t0, t1):
    return [round(t0 + (t1 - t0) * i / n, 2) for i in range(1, n)]


def auto_noise(vp):
    """آستانه‌ی سکوت رو از روی بلندی میانگین خود ویس حساب می‌کنه (ویس بلند/آروم یا نویزدار هم درست جواب بده)"""
    if SIL_DB != "auto":
        return SIL_DB
    try:
        err = run([FFMPEG, "-hide_banner", "-nostats", "-i", vp, "-vn", "-af", "volumedetect", "-f", "null", "-"], timeout=120)
        m = re.search(r"mean_volume:\s*(-?[\d.]+)\s*dB", err)
        if m:
            return f"{min(max(float(m[1]) - 14, -46), -28):.0f}dB"
    except Exception:
        log.warning("volumedetect failed")
    return "-34dB"


def cut_point(st, en):
    """نقطه‌ی برش داخل مکث: تا آخرِ مکث نزدیک می‌شه (اسلاید جدید درست قبل از شروع حرف بعدی میاد) ولی از وسط مکث عقب‌تر نمی‌ره"""
    return max((st + en) / 2, en - 0.25)


def cuts_dp(sil, n, t0, t1):
    """بهترین N-1 برش از بین همه‌ی مکث‌ها با برنامه‌ریزی پویا:
    مکث‌های قوی‌تر (بلندتر) امتیاز می‌گیرن، و طول‌های خیلی نامتعادل جریمه می‌شن. اگه شدنی نبود None"""
    if n <= 1:
        return [], 0
    cand = []
    for st, en, du in sil:
        c = cut_point(st, en)
        if t0 + MIN_SEG <= c <= t1 - MIN_SEG:
            cand.append((c, min(du, 1.2)))
    cand.sort()
    m, k_need = len(cand), n - 1
    if m < k_need:
        return None
    tgt = (t1 - t0) / n
    pen = lambda d: 0.8 * ((d - tgt) / tgt) ** 2
    NEG = -1e18
    dp = [[NEG] * m for _ in range(k_need + 1)]
    par = [[-1] * m for _ in range(k_need + 1)]
    for j in range(m):
        if cand[j][0] - t0 >= MIN_SEG:
            dp[1][j] = 2.0 * cand[j][1] - pen(cand[j][0] - t0)
    for k in range(2, k_need + 1):
        for j in range(m):
            for i in range(j):
                if dp[k - 1][i] <= NEG or cand[j][0] - cand[i][0] < MIN_SEG:
                    continue
                v = dp[k - 1][i] + 2.0 * cand[j][1] - pen(cand[j][0] - cand[i][0])
                if v > dp[k][j]:
                    dp[k][j], par[k][j] = v, i
    best, bj = NEG, -1
    for j in range(m):
        if dp[k_need][j] > NEG and t1 - cand[j][0] >= MIN_SEG:
            v = dp[k_need][j] - pen(t1 - cand[j][0])
            if v > best:
                best, bj = v, j
    if bj < 0:
        return None
    out, j = [], bj
    for k in range(k_need, 0, -1):
        out.append(round(cand[j][0], 2))
        j = par[k][j]
    return out[::-1], k_need


def cuts_pause(sil, n, t0, t1):
    r = cuts_dp(sil, n, t0, t1)
    return r if r else cuts_greedy(sil, n, t0, t1)


def cuts_greedy(sil, n, t0, t1):
    """N-1 تا از بلندترین مکث‌ها؛ اگه کم بود، بقیه از وسط بلندترین بخش‌ها. خروجی: (برش‌ها، تعداد مکث واقعی)"""
    cuts = []
    for st, en, du in sorted(sil, key=lambda x: -x[2]):
        if len(cuts) >= n - 1:
            break
        mid = (st + en) / 2
        if mid - t0 < MIN_SEG or t1 - mid < MIN_SEG or any(abs(mid - c) < MIN_SEG for c in cuts):
            continue
        cuts.append(mid)
    found = len(cuts)
    while len(cuts) < n - 1:
        pts = [t0] + sorted(cuts) + [t1]
        g, i = max((pts[k + 1] - pts[k], k) for k in range(len(pts) - 1))
        cuts.append((pts[i] + pts[i + 1]) / 2)
    return [round(c, 2) for c in sorted(cuts)], found


def _slide_chain(idx, i_label, L, out_label):
    """یه اسلاید → استریم تمام‌صفحه‌ی ۹:۱۶ (بدون بلور، بدون کادر) با زوم خیلی نرم.
    ترکیب روی بوم بزرگ‌تر (ZOOM_CANVAS برابر) انجام می‌شه تا حرکت زوم پله‌پله/لرزان نشه؛ شتاب با smoothstep نرم شروع و تموم می‌شه"""
    W, H = VIDEO_W, VIDEO_H
    cw, ch = int(W * ZOOM_CANVAS) // 2 * 2, int(H * ZOOM_CANVAS) // 2 * 2
    p = f"(on/{L})"
    e = f"({p}*{p}*(3-2*{p}))"
    z = f"1+{ZOOM_AMT}*{e}" if idx % 2 == 0 else f"1+{ZOOM_AMT}-{ZOOM_AMT}*{e}"      # یکی در میون: زوم‌این / زوم‌اوت
    return (f"[{i_label}:v]scale={cw}:{ch}:force_original_aspect_ratio=increase,crop={cw}:{ch},"
            f"zoompan=z='{z}':x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)':d={L}:s={W}x{H}:fps={FPS},"
            f"setsar=1,format=yuv420p[{out_label}]")


def make_clip(img, out, n, idx):
    """حالت ساده (برش مستقیم بین اسلایدها): یه اسلاید → کلیپ تمام‌صفحه با زوم نرم"""
    fc = _slide_chain(idx, 0, n, "v")
    run([FFMPEG, "-y", "-hide_banner", "-loglevel", "error", "-i", img, "-filter_complex", fc, "-map", "[v]",
         "-frames:v", str(n), "-r", str(FPS), "-c:v", "libx264", "-preset", PRESET, "-crf", str(CRF),
         "-threads", "1", "-pix_fmt", "yuv420p", "-an", out], timeout=240)


def run_live(cmd, total, on_frame, timeout):
    """اجرای ffmpeg با گزارش زنده‌ی پیشرفت (شماره‌ی فریمِ در حال ساخت) تا بشه به کاربر نشون داد کدوم اسلاید در حال ساخته شدنه"""
    t0 = time.time()
    with tempfile.TemporaryFile() as errf:
        p = subprocess.Popen(cmd[:1] + ["-progress", "pipe:1", "-nostats"] + cmd[1:], stdout=subprocess.PIPE, stderr=errf,
                             stdin=subprocess.DEVNULL, encoding="utf-8", errors="replace")
        try:
            for line in p.stdout:
                if time.time() - t0 > timeout:
                    raise subprocess.TimeoutExpired(cmd, timeout)
                if line.startswith("frame="):
                    try:
                        on_frame(min(int(line[6:].strip()), total))
                    except ValueError:
                        pass
            p.wait(timeout=30)
        except BaseException:
            p.kill()
            raise
        if p.returncode != 0:
            errf.seek(0)
            raise RuntimeError(errf.read().decode("utf-8", "replace")[-700:])


def build_video(imgs, nf, out, prog=None, ass=None):
    """کل ویدیو تو یه پاس ffmpeg: هر اسلاید تمام‌صفحه + زوم نرم، بین اسلایدها کراس‌فید کوتاه که دقیقاً وسط نقطه‌ی برشِ صداست؛
    پس طول هر اسلاید و همگامی با صدا تغییری نمی‌کنه. فقط یه‌بار انکود می‌شه (بدون کلیپ‌های میانی، سریع‌تر از قبل)"""
    n = len(imgs)
    half = 0 if n == 1 else max(1, min(int(round(TRANS_SEC * FPS / 2)), min(nf) // 4))
    d_f = 2 * half
    cum = [0]
    for x in nf:
        cum.append(cum[-1] + x)
    cmd = [FFMPEG, "-y", "-hide_banner", "-loglevel", "error"]
    fc = []
    for i, ip in enumerate(imgs):
        L = nf[i] + (half if i > 0 else 0) + (half if i < n - 1 else 0)     # هر اسلاید نصف ترنزیشن اضافه، دو طرف
        cmd += ["-i", ip]
        fc.append(_slide_chain(i, i, L, f"v{i}"))
    last = "v0"
    for i in range(1, n):
        fc.append(f"[{last}][v{i}]xfade=transition=fade:duration={d_f / FPS:.4f}:offset={(cum[i] - half) / FPS:.4f}[x{i}]")
        last = f"x{i}"
    if ass:       # زیرنویس روی کل ویدیو (بعد از کراس‌فید)، تو همین پاس
        fc.append(f"[{last}]{ass_filter(ass)}[sv]")
        last = "sv"
    cmd += ["-filter_complex", ";".join(fc), "-map", f"[{last}]", "-frames:v", str(cum[-1]), "-r", str(FPS),
            "-c:v", "libx264", "-preset", PRESET, "-crf", str(CRF), "-threads", "1", "-pix_fmt", "yuv420p", "-an", out]
    if prog is None:
        return run(cmd, timeout=FX_BUDGET)
    n_tr = n - 1
    state = {"txt": "", "t": 0.0}

    def on_frame(f):
        f = min(f, cum[-1])
        if n > 1 and f < cum[-1]:
            tr = next((i for i in range(1, n) if cum[i] - half <= f < cum[i] + half), 0)
        else:
            tr = 0
        i = next((k for k in range(n) if f < cum[k + 1]), n - 1)
        pct = int(f * 100 / max(cum[-1], 1))
        bar = "▰" * (pct // 10) + "▱" * (10 - pct // 10)
        if tr:
            txt = f"✨ ترنزیشن {tr} از {n_tr}…\n{bar} {pct}٪"
        else:
            txt = f"🎞 ساخت اسلاید {i + 1} از {n}…\n{bar} {pct}٪"
        if txt != state["txt"] and time.time() - state["t"] >= 2.5:     # محدودیت ویرایش پیام تلگرام
            state["txt"], state["t"] = txt, time.time()
            try:
                prog(txt)
            except Exception:
                pass

    prog(f"🎞 ساخت اسلاید 1 از {n}…\n▱▱▱▱▱▱▱▱▱▱ 0٪")
    run_live(cmd, cum[-1], on_frame, FX_BUDGET)



def mux(clips, voice, t0, dur, out, work, reencode_crf=None, ass=None):
    lst = os.path.join(work, "list.txt")
    with open(lst, "w") as f:
        for c in clips:
            f.write(f"file '{c}'\n")
    cmd = [FFMPEG, "-y", "-hide_banner", "-loglevel", "error", "-f", "concat", "-safe", "0", "-i", lst,
           "-ss", f"{t0:.3f}", "-t", f"{dur:.3f}", "-i", voice, "-map", "0:v", "-map", "1:a"]
    if reencode_crf or ass:
        if ass:
            cmd += ["-vf", ass_filter(ass)]
        cmd += ["-c:v", "libx264", "-preset", PRESET, "-crf", str(reencode_crf or CRF), "-threads", "1", "-pix_fmt", "yuv420p"]
    else:
        cmd += ["-c:v", "copy"]
    cmd += ["-af", f"loudnorm=I=-16:TP=-1.5:LRA=11,afade=t=out:st={max(dur - 0.3, 0):.3f}:d=0.3",
            "-c:a", "aac", "-b:a", "128k", "-ar", "44100", "-ac", "2", "-movflags", "+faststart",
            "-shortest", out]
    run(cmd, timeout=300)


# ───────────────────────── نمای پیش‌نمایش برش‌ها ─────────────────────────
def review_view(s):
    n = len(s["slides"])
    b = [s["t0"]] + s["cuts"] + [s["t1"]]
    mode_txt = "🔍 مکث‌محور" if s["mode"] == "pause" else "⚖️ مساوی"
    sub_txt = " • 💬 زیرنویس" if any((x or "").strip() for x in (s.get("subs") or [])) else ""
    lines = [f"🎙 صدا: {s['t1'] - s['t0']:.1f} ثانیه • 🖼 {n} اسلاید • {mode_txt}{sub_txt}"]
    if s["mode"] == "pause" and s.get("found", 0) < n - 1:
        lines.append(f"ℹ️ فقط {s.get('found', 0)} مکث مناسب پیدا شد؛ بقیه‌ی برش‌ها مساوی چیده شد.")
    lines.append("")
    for i in range(n):
        lines.append(f"{i + 1}. {b[i]:.1f} ← {b[i + 1]:.1f}   ({b[i + 1] - b[i]:.1f} ثانیه)")
    lines.append("\nبرش‌ها رو با دکمه‌ها جابه‌جا کن، بعد «ساخت ویدیو» رو بزن.")
    rows = []
    for i in range(1, n):
        rows.append([{"text": f"✂️{i} −0.5", "callback_data": f"adj:{i}:-5"},
                     {"text": "−0.1", "callback_data": f"adj:{i}:-1"},
                     {"text": "+0.1", "callback_data": f"adj:{i}:1"},
                     {"text": "+0.5", "callback_data": f"adj:{i}:5"}])
    rows.append([{"text": "⚖️ تقسیم مساوی", "callback_data": "mode:equal"},
                 {"text": "🔍 تقسیم با مکث", "callback_data": "mode:pause"}])
    rows.append([{"text": "🎬 ساخت ویدیو", "callback_data": "make"}])
    rows.append([{"text": "❌ لغو", "callback_data": "cancel"}])
    return "\n".join(lines), kb(rows)


# ───────────────────────── کارهای صف (تحلیل + رندر) ─────────────────────────
def analyze_job(uid):
    s = db.sessions.find_one({"_id": uid})
    if not s or s.get("step") != "analyzing":
        return
    chat, n = s["chat"], len(s["slides"])
    work = tempfile.mkdtemp(prefix="rv_")
    try:
        stage(uid, "download")
        vp = tg_download(s["voice"]["fid"], os.path.join(work, "voice"))
        log.info("analyze: downloaded %s bytes", os.path.getsize(vp))
        stage(uid, "ffmpeg-silencedetect")
        noise = auto_noise(vp)
        log.info("silence threshold: %s", noise)
        err = run([FFMPEG, "-hide_banner", "-nostats", "-i", vp, "-vn",
                   "-af", f"silencedetect=noise={noise}:d={SIL_MIN}", "-f", "null", "-"], timeout=120)
        dur, sil = parse_silence(err)
        dur = dur or float(s["voice"].get("dur") or 0)
        if dur <= 0:
            raise ValueError("bad_audio")
        if dur > MAX_AUDIO + 2:
            db.sessions.update_one({"_id": uid}, {"$set": {"step": "voice"}})
            return say(chat, f"⚠️ ویس {dur:.0f} ثانیه‌ست؛ حداکثر {MAX_AUDIO} ثانیه مجازه. یه ویس کوتاه‌تر بفرست.")
        t0, t1 = 0.0, dur
        if sil and sil[0][0] <= 0.1:
            t0 = max(0.0, sil[0][1] - 0.15)
        if sil and sil[-1][1] >= dur - 0.1 and sil[-1][0] > 0.1:
            t1 = min(dur, sil[-1][0] + 0.4)
        if t1 - t0 < n * MIN_SEG:
            db.sessions.update_one({"_id": uid}, {"$set": {"step": "voice"}})
            return say(chat, f"⚠️ ویس برای {n} اسلاید خیلی کوتاهه (حداقل {n * MIN_SEG:.0f} ثانیه گفتار لازمه). ویس بلندتری بفرست.")
        internal = [list(x) for x in sil if x[0] > 0.1 and x[1] < dur - 0.1]
        cuts, found = cuts_pause(internal, n, t0, t1)
        s2 = {"step": "review", "dur": dur, "t0": round(t0, 2), "t1": round(t1, 2), "sil": internal,
              "mode": "pause", "cuts": cuts, "found": found, "t": now()}
        db.sessions.update_one({"_id": uid}, {"$set": s2})
        s.update(s2)
        text, markup = review_view(s)
        say(chat, text, markup)
    except Exception as e:
        log.exception("analyze failed")
        db.sessions.update_one({"_id": uid}, {"$set": {"step": "voice"}})
        say(chat, "❌ تحلیل ویس انجام نشد. یه ویس دیگه بفرست." + (f"\n\n{e}" if DEBUG else ""))
    finally:
        shutil.rmtree(work, ignore_errors=True)


def render_job(uid):
    s = db.sessions.find_one({"_id": uid})
    if not s or s.get("step") != "queued":
        return
    db.sessions.update_one({"_id": uid}, {"$set": {"step": "rendering"}})
    chat = s["chat"]
    st = say(chat, "⏳ شروع ساخت ویدیو…")
    pmid = (st.get("result") or {}).get("message_id")

    def prog(t):
        if pmid:
            edit(chat, pmid, t)

    work = tempfile.mkdtemp(prefix="rv_")
    try:
        slides, n = s["slides"], len(s["slides"])
        bounds = [s["t0"]] + s["cuts"] + [s["t1"]]
        fr = [round((b - bounds[0]) * FPS) for b in bounds]   # فریم تجمعی؛ بدون خطای انباشته‌ی همگام‌سازی
        prog("⬇️ دریافت ویس…")
        stage(uid, "render-download")
        vp = tg_download(s["voice"]["fid"], os.path.join(work, "voice"))
        nf = [max(fr[i + 1] - fr[i], 2) for i in range(n)]
        ass = None
        subs = (list(s.get("subs") or []) + [""] * n)[:n]
        if SUBS_OK and any((x or "").strip() for x in subs):
            cumf = [0]
            for x in nf:
                cumf.append(cumf[-1] + x)
            ass = os.path.join(work, "subs.ass")
            write_ass(ass, subs, cumf)
        imgs = []
        for i, sl in enumerate(slides):
            prog(f"📥 دریافت اسلاید {i + 1} از {n}…")
            stage(uid, f"render-dl-{i + 1}")
            imgs.append(tg_download(sl["fid"], os.path.join(work, f"s{i}")))
        clips = None
        if FX_OK:      # کراس‌فید؛ اگه خطا داد، خودکار برش مستقیم (بدون کراس‌فید) ساخته می‌شه
            try:
                stage(uid, "render-video")
                vo = os.path.join(work, "video.mp4")
                build_video(imgs, nf, vo, prog, ass)
                clips = [vo]
                ass = None      # تو ویدیو سوخته شده
            except Exception as e:
                log.exception("crossfade render failed; falling back to hard cuts")
                prog("⚠️ ساخت کراس‌فید خطا داد؛ نسخه‌ی ساده ساخته می‌شه…"
                     + (f"\n{str(e)[-300:]}" if DEBUG else ""))
        if clips is None:
            clips = []
            for i, ip in enumerate(imgs):
                prog(f"🎞 ساخت اسلاید {i + 1} از {n}…")
                stage(uid, f"render-clip-{i + 1}")
                cp = os.path.join(work, f"c{i}.mp4")
                make_clip(ip, cp, nf[i], i)
                clips.append(cp)
        prog("🎚 ترکیب با صدای گوینده…")
        stage(uid, "render-mux")
        out = os.path.join(work, "out.mp4")
        dur = bounds[-1] - bounds[0]
        mux(clips, vp, bounds[0], dur, out, work, ass=ass)
        if os.path.getsize(out) > 49 * 1024 * 1024:
            prog("🗜 حجم زیاده، فشرده‌سازی…")
            mux(clips, vp, bounds[0], dur, out, work, reencode_crf=34, ass=ass)
        prog("📤 در حال ارسال…")
        with open(out, "rb") as f:
            r = tg_upload("sendVideo", {"chat_id": chat, "caption": "✅ ویدیوت آماده‌ست! برای ساخت بعدی /new",
                                        "supports_streaming": "true", "width": VIDEO_W, "height": VIDEO_H,
                                        "duration": int(dur)}, {"video": f})
        if not r.get("ok"):
            with open(out, "rb") as f:
                r = tg_upload("sendDocument", {"chat_id": chat, "caption": "✅ ویدیوت آماده‌ست!"}, {"document": f})
        if not r.get("ok"):
            raise RuntimeError("send: " + str(r.get("description")))
        if pmid:
            tg("deleteMessage", chat_id=chat, message_id=pmid)
        db.sessions.delete_one({"_id": uid})
    except Exception as e:
        log.exception("render failed")
        quota_refund(uid)
        db.sessions.update_one({"_id": uid}, {"$set": {"step": "review"}})
        prog("❌ ساخت ویدیو ناموفق بود (سهمیه‌ت برگشت). دوباره امتحان کن." + (f"\n\n{str(e)[-500:]}" if DEBUG else ""))
    finally:
        shutil.rmtree(work, ignore_errors=True)


def worker(q, kind):
    last_clean = time.time()
    while True:
        try:
            uid = q.popleft()
        except IndexError:
            time.sleep(0.5)
            if time.time() - last_clean > 1800:   # پاکسازی نشست‌های قدیمی
                last_clean = time.time()
                try:
                    db.sessions.delete_many({"t": {"$lt": now() - timedelta(hours=24)}, "step": {"$nin": list(BUSY)}})
                except Exception:
                    log.exception("cleanup failed")
            continue
        if kind == "render":
            with state_lock:
                busy_now["v"] = True
        log.info("job %s start uid=%s", kind, uid)
        try:
            analyze_job(uid) if kind == "analyze" else render_job(uid)
        except Exception:
            log.exception("job crashed")
        finally:
            log.info("job %s done uid=%s", kind, uid)
            if kind == "render":
                with state_lock:
                    busy_now["v"] = False


# ───────────────────────── هندلرها ─────────────────────────
def help_text():
    return ("🎬 سلام! از اسلایدها و ویس گوینده‌ت ویدیوی ۹:۱۶ مخصوص ریلز می‌سازم.\n\n"
            f"۱) اسلایدها (عکس) رو به ترتیب بفرست — تا {MAX_SLIDES} تا\n"
            "۲) با دکمه‌ی «تمام شد» برو مرحله‌ی بعد\n"
            + ("۳) (اختیاری) زیرنویس همه‌ی اسلایدها رو تو یه پیام بفرست؛ بین هر اسلاید یه خط فقط با - بذار\n" if SUBS_OK else "")
            + f"{'۴' if SUBS_OK else '۳'}) ویس کامل گوینده رو بفرست (تا {MAX_AUDIO} ثانیه)؛ خودم بین اسلایدها تقسیمش می‌کنم\n"
            f"{'۵' if SUBS_OK else '۴'}) برش‌ها رو اگه لازم بود تنظیم کن و «ساخت ویدیو» رو بزن\n\n"
            "/new شروع تازه • /cancel لغو")


def new_session(uid, chat):
    s = {"_id": uid, "chat": chat, "step": "slides", "slides": [], "t": now()}
    db.sessions.replace_one({"_id": uid}, s, upsert=True)
    return s


def subs_prompt(n, extra=""):
    return (f"✅ {n} اسلاید ثبت شد.{extra}\n\n"
            "✍️ حالا زیرنویس اسلایدها رو به ترتیب، همه تو یه پیام بفرست. بین زیرنویس هر اسلاید یه خط فقط با - بذار:\n\n"
            "متن اسلاید اول\n-\nمتن اسلاید دوم\n-\nمتن اسلاید سوم\n\n"
            f"• تعداد بخش‌ها باید {n} تا باشه\n"
            "• اسلایدی که زیرنویس نمی‌خواد، جاش رو خالی بذار\n"
            "• زیرنویس نمی‌خوای؟ دکمه‌ی پایین رو بزن")


def handle_subs(uid, chat, s, text):
    n = len(s["slides"])
    parts = parse_subs(text)
    if len(parts) == n + 1 and (not parts[0] or not parts[-1]):      # خط‌تیره‌ی اضافه اول یا آخر پیام
        parts = parts[1:] if not parts[0] else parts[:-1]
    if len(parts) != n:
        return say(chat, f"⚠️ {len(parts)} بخش زیرنویس پیدا کردم ولی {n} اسلاید داری.\n\n"
                         "بین زیرنویس هر اسلاید یه خط فقط با - بذار و دوباره همه رو تو یه پیام بفرست. "
                         "اسلایدی که زیرنویس نمی‌خواد، جاش رو خالی بذار.")
    if not any(parts):
        return say(chat, "⚠️ همه‌ی زیرنویس‌ها خالیه. اگه زیرنویس نمی‌خوای، همین‌طوری ویس رو بفرست.")
    long_ = [str(i + 1) for i, p in enumerate(parts) if len(p) > SUB_MAX]
    if long_:
        return say(chat, f"⚠️ زیرنویس اسلاید {'، '.join(long_)} از {SUB_MAX} حرف بلندتره. کوتاه‌ترش کن و دوباره بفرست.")
    db.sessions.update_one({"_id": uid}, {"$set": {"subs": parts, "step": "voice", "t": now()}})
    prev = "\n".join(f"{i + 1}. " + ((p.replace("\n", " ")[:30] + ("…" if len(p) > 30 else "")) if p else "—") for i, p in enumerate(parts))
    say(chat, f"✅ زیرنویس ثبت شد:\n{prev}\n\n🎙 حالا ویس کامل گوینده رو بفرست.\n(برای اصلاح زیرنویس، دوباره بفرستش.)")


def on_message(msg):
    if msg["chat"]["type"] != "private":
        return
    chat = msg["chat"]["id"]
    uid = (msg.get("from") or {}).get("id", chat)
    text = (msg.get("text") or "").strip()
    s = db.sessions.find_one({"_id": uid})

    if text.startswith("/"):
        cmd = text[1:].split()[0].split("@")[0].lower()
        if cmd in ("start", "help"):
            say(chat, help_text())
        elif cmd == "debug":
            ta, tr = THREADS.get("analyze"), THREADS.get("render")
            say(chat, f"ffmpeg: {FFVER}\nترد تحلیل: {'زنده' if ta and ta.is_alive() else 'مرده'} (صف {len(ajobs)})\n"
                      f"ترد رندر: {'زنده' if tr and tr.is_alive() else 'مرده'} (صف {len(jobs)})\n"
                      f"زیرنویس: {'فعال، فونت ' + str(SUB_FAMILY) if SUBS_OK else 'غیرفعال (فونت یا فیلتر ass پیدا نشد)'}\n"
                      f"نشست تو: {(s or {}).get('step', '-')} / {(s or {}).get('stage', '-')}")
        elif cmd in ("new", "cancel"):
            if s and s.get("step") in BUSY:
                return say(chat, "⏳ ویدیوی قبلی هنوز در حال پردازشه؛ کمی صبر کن.")
            if cmd == "new":
                new_session(uid, chat)
                say(chat, "🖼 اسلایدها رو به ترتیب بفرست.")
            else:
                db.sessions.delete_one({"_id": uid})
                say(chat, "لغو شد. برای شروع /new")
        return

    photo, doc = msg.get("photo"), msg.get("document") or {}
    voice = msg.get("voice") or msg.get("audio")
    if not voice and (doc.get("mime_type") or "").startswith("audio/"):
        voice = doc
    img_fid = None
    if photo:
        img_fid = photo[-1]["file_id"]
    elif (doc.get("mime_type") or "").startswith("image/"):
        img_fid = doc["file_id"]

    if text and not img_fid and not voice and SUBS_OK and s and s.get("step") in ("subs", "voice"):
        return handle_subs(uid, chat, s, text)
    if not img_fid and not voice:
        return say(chat, help_text())
    if s and s.get("step") in BUSY:
        return say(chat, "⏳ ویدیوی قبلی هنوز در حال پردازشه؛ کمی صبر کن.")
    if not s:
        s = new_session(uid, chat)
    step = s["step"]

    if img_fid:
        if step != "slides":
            return say(chat, "اسلایدها قبلاً ثبت شده. برای شروع از اول /new رو بزن.")
        db.sessions.update_one({"_id": uid}, {"$push": {"slides": {"fid": img_fid, "mid": msg["message_id"]}},
                                              "$set": {"chat": chat, "t": now()}})
        key = msg.get("media_group_id") or f"m{msg['message_id']}"
        if db.sessions.find_one_and_update({"_id": uid, "last_key": {"$ne": key}}, {"$set": {"last_key": key}}):
            say(chat, "📥 اسلاید دریافت شد. اگه بیشتر داری بفرست، وگرنه دکمه‌ی زیر رو بزن.",
                kb([[{"text": "✅ تمام شد، برو سراغ ویس", "callback_data": "done"}]]))
        return

    # ویس
    if step == "subs":
        return say(chat, "✍️ اول زیرنویس اسلایدها رو بفرست، یا دکمه‌ی «بدون زیرنویس» رو بزن.")
    if step == "slides" and not s["slides"]:
        return say(chat, "اول اسلایدها (عکس) رو بفرست 🖼")
    if (voice.get("file_size") or 0) > 20 * 1024 * 1024:
        return say(chat, "⚠️ حجم فایل صوتی بیشتر از ۲۰ مگابایته (محدودیت تلگرام برای ربات‌ها).")
    if (voice.get("duration") or 0) > MAX_AUDIO + 2:
        return say(chat, f"⚠️ حداکثر طول ویس {MAX_AUDIO} ثانیه‌ست.")
    slides = sorted(s["slides"], key=lambda x: x["mid"])[:MAX_SLIDES]
    db.sessions.update_one({"_id": uid}, {"$set": {"slides": slides, "chat": chat, "step": "analyzing", "t": now(),
                                                   "voice": {"fid": voice["file_id"], "dur": voice.get("duration", 0)}},
                                     "$unset": {"stage": ""}})
    say(chat, f"🔍 در حال تحلیل ویس و تقسیم بین {len(slides)} اسلاید…")
    ajobs.append(uid)
    threading.Timer(45, watchdog, args=(uid, chat)).start()


def on_callback(cq):
    data, uid = cq.get("data", ""), cq["from"]["id"]
    m = cq.get("message") or {}
    chat, mid = (m.get("chat") or {}).get("id"), m.get("message_id")

    def ans(text=None, alert=False):
        tg("answerCallbackQuery", callback_query_id=cq["id"], **({"text": text, "show_alert": alert} if text else {}))

    s = db.sessions.find_one({"_id": uid})
    if not s or not chat:
        return ans("نشست منقضی شده؛ /new رو بزن.", True)
    step = s.get("step")

    if data == "cancel":
        if step in BUSY:
            return ans("در حال پردازشه، کمی صبر کن.", True)
        db.sessions.delete_one({"_id": uid})
        ans()
        return edit(chat, mid, "لغو شد. برای شروع /new")

    if data == "done":
        if step != "slides":
            return ans()
        n = len(s["slides"])
        if n == 0:
            return ans("اول حداقل یه اسلاید بفرست.", True)
        extra = f"\n(فقط {MAX_SLIDES} اسلاید اول استفاده می‌شه)" if n > MAX_SLIDES else ""
        slides = sorted(s["slides"], key=lambda x: x["mid"])[:MAX_SLIDES]
        ans()
        if SUBS_OK:
            db.sessions.update_one({"_id": uid}, {"$set": {"step": "subs", "slides": slides, "t": now()}, "$unset": {"subs": ""}})
            return edit(chat, mid, subs_prompt(len(slides), extra), kb([[{"text": "⏭ بدون زیرنویس", "callback_data": "nosub"}]]))
        db.sessions.update_one({"_id": uid}, {"$set": {"step": "voice", "t": now()}})
        return edit(chat, mid, f"✅ {min(n, MAX_SLIDES)} اسلاید ثبت شد.{extra}\n\n🎙 حالا ویس کامل گوینده رو بفرست.")

    if data == "nosub":
        if step != "subs":
            return ans()
        db.sessions.update_one({"_id": uid}, {"$set": {"step": "voice", "t": now()}, "$unset": {"subs": ""}})
        ans()
        return edit(chat, mid, "✅ بدون زیرنویس.\n\n🎙 حالا ویس کامل گوینده رو بفرست.")

    if step != "review":
        return ans("این مرحله دیگه فعال نیست.", True)

    if data.startswith("mode:"):
        mode = data[5:]
        n = len(s["slides"])
        if mode == "equal":
            cuts, found = cuts_equal(n, s["t0"], s["t1"]), 0
        else:
            cuts, found = cuts_pause(s.get("sil", []), n, s["t0"], s["t1"])
        mode = "equal" if mode == "equal" else "pause"
        db.sessions.update_one({"_id": uid}, {"$set": {"mode": mode, "cuts": cuts, "found": found, "t": now()}})
        s.update(mode=mode, cuts=cuts, found=found)
        ans()
        text, markup = review_view(s)
        return edit(chat, mid, text, markup)

    if data.startswith("adj:"):
        try:
            _, i, d = data.split(":")
            i, d = int(i), int(d) / 10
            b = [s["t0"]] + s["cuts"] + [s["t1"]]
            new = round(min(max(b[i] + d, b[i - 1] + MIN_ADJ), b[i + 1] - MIN_ADJ), 2)
        except Exception:
            return ans()
        if new == b[i]:
            return ans("بیشتر از این نمی‌شه جابه‌جا کرد.")
        cuts = list(s["cuts"])
        cuts[i - 1] = new
        db.sessions.update_one({"_id": uid}, {"$set": {"cuts": cuts, "t": now()}})
        s["cuts"] = cuts
        ans()
        text, markup = review_view(s)
        return edit(chat, mid, text, markup)

    if data == "make":
        if not db.sessions.find_one_and_update({"_id": uid, "step": "review"}, {"$set": {"step": "queued"}}):
            return ans()
        if not quota_take(uid):
            db.sessions.update_one({"_id": uid}, {"$set": {"step": "review"}})
            return ans(f"سهمیه‌ی امروزت ({DAILY_LIMIT} ویدیو) تموم شده؛ فردا دوباره امتحان کن.", True)
        pos = len(jobs) + (1 if busy_now["v"] else 0)
        ans()
        edit(chat, mid, f"📋 در صف ساخت قرار گرفتی ({pos + 1}). به‌محض آماده شدن ویدیو براخودت می‌فرستم.")
        jobs.append(uid)
        return


@app.get("/")
def health():
    return "ok"


@app.post("/hook")
def hook():
    if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != HOOK_SECRET:
        return "forbidden", 403
    ensure_workers()
    upd = request.get_json(silent=True) or {}
    try:
        if upd.get("callback_query"):
            on_callback(upd["callback_query"])
        elif upd.get("message"):
            on_message(upd["message"])
    except Exception:
        log.exception("hook error")
    return "ok"


def setup():
    # کارهای نیمه‌تمومِ قبل از ری‌استارت (صف داخل حافظه بود) برمی‌گردن به مرحله‌ی قبل
    for st_from, st_to, msg in (("queued", "review", "🔄 سرور ری‌استارت شد و ساخت ویدیو قطع شد. دوباره «ساخت ویدیو» رو بزن."),
                                ("rendering", "review", "🔄 سرور ری‌استارت شد و ساخت ویدیو قطع شد. دوباره «ساخت ویدیو» رو بزن."),
                                ("analyzing", "voice", "🔄 سرور ری‌استارت شد و تحلیل ویس قطع شد. ویس رو دوباره بفرست.")):
        for d in list(db.sessions.find({"step": st_from})):
            db.sessions.update_one({"_id": d["_id"]}, {"$set": {"step": st_to}})
            say(d["chat"], msg)   # کاربر دیگه بی‌خبر گیر نمی‌کنه
    r = tg("setWebhook", url=f"{BASE_URL}/hook", secret_token=HOOK_SECRET,
           allowed_updates=["message", "callback_query"])
    tg("setMyCommands", commands=[{"command": "new", "description": "ساخت ویدیوی جدید"},
                                  {"command": "cancel", "description": "لغو"},
                                  {"command": "help", "description": "راهنما"}])
    log.info("webhook: %s", r)


setup()
_ens_lock = threading.Lock()


def ensure_workers():
    """تردهای کارگر رو (دوباره) راه می‌اندازه. بعد از fork گانیکورن (مثلا preload) یا مرگ ترد لازمه"""
    with _ens_lock:
        for k, q in (("analyze", ajobs), ("render", jobs)):
            t = THREADS.get(k)
            if not t or not t.is_alive():
                t = threading.Thread(target=worker, args=(q, k), daemon=True)
                THREADS[k] = t
                t.start()
                log.info("worker %s started (pid=%s)", k, os.getpid())


ensure_workers()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 10000)))
