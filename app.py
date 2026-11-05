# -*- coding: utf-8 -*-
"""
Reel Maker — ربات ساخت ریلز اسلایدی با ویس گوینده
Stack (مثل app-6): Flask + MongoDB(pymongo / mongomock) + وب‌هوک تلگرام
- کاربر اسلایدها (عکس) رو می‌فرسته، بعد یه ویس کامل از گوینده
- ویس با ffmpeg silencedetect روی مکث‌ها بین اسلایدها تقسیم می‌شه (یا مساوی)، با دکمه قابل تنظیمه
- خروجی: ویدیوی ۹:۱۶ با پس‌زمینه‌ی بلور، زوم/پن ملایم، فید بین اسلایدها و صدای نرمال‌شده
- ساخت ویدیو در یه صف تک‌نفره (مناسب پلن رایگان Render: رم کم / CPU ضعیف)
اجرا: gunicorn app:app -w 1 --threads 4 -t 120   (حتما یک worker، چون صف داخل حافظه‌ست)
"""
import os, re, time, hashlib, logging, shutil, subprocess, tempfile, threading, queue
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
CRF         = int(os.environ.get("CRF", "27"))
SIL_DB      = os.environ.get("SIL_DB", "-32dB")             # آستانه‌ی سکوت
SIL_MIN     = float(os.environ.get("SIL_MIN", "0.3"))       # حداقل طول مکث (ثانیه)
DEBUG       = os.environ.get("DEBUG", "") == "1"            # علت دقیق خطا رو برای کاربر نشون می‌ده
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
jobs = queue.Queue()     # صف رندر ویدیو
ajobs = queue.Queue()    # صف تحلیل ویس (جدا از رندر تا پشت رندر کند گیر نکنه)
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


def tg_download(file_id, dest_base):
    """فایل رو دانلود می‌کنه و مسیر نهایی (با پسوند درست) رو برمی‌گردونه"""
    r = tg("getFile", file_id=file_id)
    if not r.get("ok"):
        raise RuntimeError("getFile: " + str(r.get("description")))
    path = r["result"]["file_path"]
    dest = dest_base + (os.path.splitext(path)[1] or "")
    with requests.get(f"https://api.telegram.org/file/bot{BOT_TOKEN}/{path}", stream=True, timeout=60) as resp:
        resp.raise_for_status()
        with open(dest, "wb") as f:
            for ch in resp.iter_content(65536):
                f.write(ch)
    return dest


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
              f"ترد تحلیل زنده: {'بله' if th and th.is_alive() else 'نه'} • صف: {ajobs.qsize()}\n"
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


def cuts_pause(sil, n, t0, t1):
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


def make_clip(img, out, n, idx):
    """یه اسلاید → کلیپ: پس‌زمینه‌ی بلور + عکس وسط + زوم/پن ملایم + فید ورودی/خروجی"""
    W, H = VIDEO_W, VIDEO_H
    bw, bh = W * 3 // 2, H * 3 // 2          # ترکیب در سایز بزرگ‌تر تا زوم نلرزه
    if idx % 3 == 0:
        z, x, y = f"1+0.12*on/{n}", "iw/2-(iw/zoom/2)", "ih/2-(ih/zoom/2)"
    elif idx % 3 == 1:
        z, x, y = f"1.12-0.12*on/{n}", "iw/2-(iw/zoom/2)", "ih/2-(ih/zoom/2)"
    else:
        z, x, y = "1.1", f"(iw-iw/zoom)*on/{n}", "ih/2-(ih/zoom/2)"
    fd = 0.2
    fo = max(n / FPS - fd, 0)
    fc = (f"[0:v]split[a][b];"
          f"[a]scale={bw}:{bh}:force_original_aspect_ratio=increase,crop={bw}:{bh},boxblur=25:3,eq=brightness=-0.08[bg];"
          f"[b]scale={bw}:{bh}:force_original_aspect_ratio=decrease[fg];"
          f"[bg][fg]overlay=(W-w)/2:(H-h)/2,"
          f"zoompan=z='{z}':x='{x}':y='{y}':d={n}:s={W}x{H}:fps={FPS},"
          f"fade=t=in:st=0:d={fd},fade=t=out:st={fo:.3f}:d={fd},format=yuv420p[v]")
    run([FFMPEG, "-y", "-hide_banner", "-loglevel", "error", "-i", img, "-filter_complex", fc, "-map", "[v]",
         "-frames:v", str(n), "-r", str(FPS), "-c:v", "libx264", "-preset", PRESET, "-crf", str(CRF),
         "-threads", "1", "-pix_fmt", "yuv420p", "-an", out], timeout=240)


def mux(clips, voice, t0, dur, out, work, reencode_crf=None):
    lst = os.path.join(work, "list.txt")
    with open(lst, "w") as f:
        for c in clips:
            f.write(f"file '{c}'\n")
    cmd = [FFMPEG, "-y", "-hide_banner", "-loglevel", "error", "-f", "concat", "-safe", "0", "-i", lst,
           "-ss", f"{t0:.3f}", "-t", f"{dur:.3f}", "-i", voice, "-map", "0:v", "-map", "1:a"]
    if reencode_crf:
        cmd += ["-c:v", "libx264", "-preset", PRESET, "-crf", str(reencode_crf), "-threads", "1", "-pix_fmt", "yuv420p"]
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
    lines = [f"🎙 صدا: {s['t1'] - s['t0']:.1f} ثانیه • 🖼 {n} اسلاید • {mode_txt}"]
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
        err = run([FFMPEG, "-hide_banner", "-nostats", "-i", vp, "-vn",
                   "-af", f"silencedetect=noise={SIL_DB}:d={SIL_MIN}", "-f", "null", "-"], timeout=120)
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
        clips = []
        for i, sl in enumerate(slides):
            prog(f"🎞 ساخت اسلاید {i + 1} از {n}…")
            stage(uid, f"render-clip-{i + 1}")
            ip = tg_download(sl["fid"], os.path.join(work, f"s{i}"))
            cp = os.path.join(work, f"c{i}.mp4")
            make_clip(ip, cp, max(fr[i + 1] - fr[i], 2), i)
            os.remove(ip)
            clips.append(cp)
        prog("🎚 ترکیب با صدای گوینده…")
        stage(uid, "render-mux")
        out = os.path.join(work, "out.mp4")
        dur = bounds[-1] - bounds[0]
        mux(clips, vp, bounds[0], dur, out, work)
        if os.path.getsize(out) > 49 * 1024 * 1024:
            prog("🗜 حجم زیاده، فشرده‌سازی…")
            mux(clips, vp, bounds[0], dur, out, work, reencode_crf=34)
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
    while True:
        try:
            uid = q.get(timeout=1800)
        except queue.Empty:
            try:   # پاکسازی نشست‌های قدیمی
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
            q.task_done()


# ───────────────────────── هندلرها ─────────────────────────
def help_text():
    return ("🎬 سلام! از اسلایدها و ویس گوینده‌ت ویدیوی ۹:۱۶ مخصوص ریلز می‌سازم.\n\n"
            f"۱) اسلایدها (عکس) رو به ترتیب بفرست — تا {MAX_SLIDES} تا\n"
            "۲) با دکمه‌ی «تمام شد» برو مرحله‌ی بعد\n"
            f"۳) ویس کامل گوینده رو بفرست (تا {MAX_AUDIO} ثانیه)؛ خودم بین اسلایدها تقسیمش می‌کنم\n"
            "۴) برش‌ها رو اگه لازم بود تنظیم کن و «ساخت ویدیو» رو بزن\n\n"
            "/new شروع تازه • /cancel لغو")


def new_session(uid, chat):
    s = {"_id": uid, "chat": chat, "step": "slides", "slides": [], "t": now()}
    db.sessions.replace_one({"_id": uid}, s, upsert=True)
    return s


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
            say(chat, f"ffmpeg: {FFVER}\nترد تحلیل: {'زنده' if ta and ta.is_alive() else 'مرده'} (صف {ajobs.qsize()})\n"
                      f"ترد رندر: {'زنده' if tr and tr.is_alive() else 'مرده'} (صف {jobs.qsize()})\n"
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
    ajobs.put(uid)
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
        db.sessions.update_one({"_id": uid}, {"$set": {"step": "voice", "t": now()}})
        ans()
        extra = f"\n(فقط {MAX_SLIDES} اسلاید اول استفاده می‌شه)" if n > MAX_SLIDES else ""
        return edit(chat, mid, f"✅ {min(n, MAX_SLIDES)} اسلاید ثبت شد.{extra}\n\n🎙 حالا ویس کامل گوینده رو بفرست.")

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
        pos = jobs.qsize() + (1 if busy_now["v"] else 0)
        ans()
        edit(chat, mid, f"📋 در صف ساخت قرار گرفتی ({pos + 1}). به‌محض آماده شدن ویدیو براخودت می‌فرستم.")
        jobs.put(uid)
        return


@app.get("/")
def health():
    return "ok"


@app.post("/hook")
def hook():
    if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != HOOK_SECRET:
        return "forbidden", 403
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
for _k, _q in (("analyze", ajobs), ("render", jobs)):
    THREADS[_k] = threading.Thread(target=worker, args=(_q, _k), daemon=True)
    THREADS[_k].start()
log.info("workers started")

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 10000)))
