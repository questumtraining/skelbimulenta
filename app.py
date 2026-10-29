#!/usr/bin/env python3
"""Questum Training bulletin board. Python standard library + SQLite only."""
from __future__ import annotations

import csv
from contextlib import contextmanager
import hashlib
import html
import io
import os
import re
import secrets
import smtplib
import sqlite3
import ssl
import string
import time
from datetime import datetime, timezone
from email.message import EmailMessage
from email.parser import BytesParser
from email.policy import default
from http import HTTPStatus
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, unquote, urlparse

from cryptography.fernet import Fernet, InvalidToken


ROOT = Path(__file__).resolve().parent
DB_PATH = Path(os.environ.get("QUESTUM_DB_PATH", ROOT / "data" / "questum.sqlite3"))
HOST = os.environ.get("QUESTUM_HOST", "127.0.0.1")
PORT = int(os.environ.get("QUESTUM_PORT", "8000"))
SESSION_HOURS = 12
PBKDF2_ROUNDS = 310_000


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


@contextmanager
def db():
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(DB_PATH, timeout=15)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA journal_mode = WAL")
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def init_db() -> None:
    with db() as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS users (
          id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL COLLATE NOCASE UNIQUE,
          role TEXT NOT NULL CHECK(role IN ('admin','participant')),
          password_hash TEXT NOT NULL, active INTEGER NOT NULL DEFAULT 1,
          created_at TEXT NOT NULL, updated_at TEXT NOT NULL,
          invite_secret TEXT, invite_status TEXT NOT NULL DEFAULT '', invite_updated_at TEXT
        );
        CREATE TABLE IF NOT EXISTS groups (
          id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE COLLATE NOCASE,
          created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS user_groups (
          user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
          group_id INTEGER NOT NULL REFERENCES groups(id) ON DELETE CASCADE,
          PRIMARY KEY(user_id, group_id)
        );
        CREATE TABLE IF NOT EXISTS sessions (
          token_hash TEXT PRIMARY KEY, user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
          csrf TEXT NOT NULL, expires_at INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS announcements (
          id INTEGER PRIMARY KEY, title TEXT NOT NULL, body TEXT NOT NULL,
          author_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
          visibility TEXT NOT NULL CHECK(visibility IN ('all','group')),
          group_id INTEGER REFERENCES groups(id) ON DELETE SET NULL,
          attachment_url TEXT NOT NULL DEFAULT '', published INTEGER NOT NULL DEFAULT 0,
          created_at TEXT NOT NULL, updated_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS mentors (
          id INTEGER PRIMARY KEY,
          name TEXT NOT NULL, email TEXT NOT NULL DEFAULT '', phone TEXT NOT NULL DEFAULT '',
          bio TEXT NOT NULL DEFAULT '', specialties TEXT NOT NULL DEFAULT '',
          active INTEGER NOT NULL DEFAULT 1, created_at TEXT NOT NULL, updated_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS mentor_photos (
          mentor_id INTEGER PRIMARY KEY REFERENCES mentors(id) ON DELETE CASCADE,
          content_type TEXT NOT NULL, data BLOB NOT NULL, updated_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS ratings (
          id INTEGER PRIMARY KEY, mentor_id INTEGER NOT NULL REFERENCES mentors(id) ON DELETE CASCADE,
          user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
          stars INTEGER NOT NULL CHECK(stars BETWEEN 1 AND 5), comment TEXT NOT NULL DEFAULT '',
          comment_hidden INTEGER NOT NULL DEFAULT 0, created_at TEXT NOT NULL, updated_at TEXT NOT NULL,
          UNIQUE(mentor_id, user_id)
        );
        CREATE INDEX IF NOT EXISTS idx_announcement_created ON announcements(created_at DESC);
        CREATE INDEX IF NOT EXISTS idx_ratings_mentor ON ratings(mentor_id);
        CREATE INDEX IF NOT EXISTS idx_sessions_expiry ON sessions(expires_at);
        """)
        user_columns = {row["name"] for row in c.execute("PRAGMA table_info(users)")}
        if "invite_secret" not in user_columns:
            c.execute("ALTER TABLE users ADD COLUMN invite_secret TEXT")
        if "invite_status" not in user_columns:
            c.execute("ALTER TABLE users ADD COLUMN invite_status TEXT NOT NULL DEFAULT ''")
        if "invite_updated_at" not in user_columns:
            c.execute("ALTER TABLE users ADD COLUMN invite_updated_at TEXT")

        # Mentors are passive records managed by admins: drop legacy mentor accounts, keep their profiles.
        mentor_columns = {row["name"] for row in c.execute("PRAGMA table_info(mentors)")}
        if "user_id" in mentor_columns:
            for account in c.execute("SELECT u.id,u.name,u.email,u.active FROM users u LEFT JOIN mentors m ON m.user_id=u.id WHERE u.role='mentor' AND m.id IS NULL").fetchall():
                c.execute("INSERT INTO mentors(user_id,name,email,active,created_at,updated_at) VALUES(?,?,?,?,?,?)", (account["id"],account["name"],account["email"],account["active"],now(),now()))
            c.execute("UPDATE mentors SET user_id=NULL WHERE user_id IS NOT NULL")
        c.execute("DELETE FROM users WHERE role='mentor'")
        c.execute("UPDATE announcements SET visibility='all',group_id=NULL,published=0 WHERE visibility='mentors'")


MAX_PHOTO_BYTES = 2 * 1024 * 1024


def photo_type(raw: bytes) -> str | None:
    if raw.startswith(b"\xff\xd8\xff"):
        return "image/jpeg"
    if raw.startswith(b"\x89PNG\r\n\x1a\n"):
        return "image/png"
    if raw[:4] == b"RIFF" and raw[8:12] == b"WEBP":
        return "image/webp"
    return None


def avatar_html(mentor, large: bool = False) -> str:
    cls = "avatar large" if large else "avatar"
    if mentor["photo_v"]:
        return f'<div class="{cls}"><img src="/mentor/photo?id={mentor["id"]}&amp;v={quote(str(mentor["photo_v"]))}" alt="{esc(mentor["name"])}"></div>'
    return f'<div class="{cls}">{esc((mentor["name"] or "?")[:1].upper())}</div>'



def save_mentor(fields: dict, photo: tuple[str, bytes] | None = None, remove_photo: bool = False, mentor_id: int | None = None) -> int:
    """Single backend service for creating/updating a mentor record (profile data and photo)."""
    name = (fields.get("name") or "").strip()
    email = (fields.get("email") or "").strip()
    if not name:
        raise ValueError("Įrašykite mentoriaus vardą.")
    if email and "@" not in email:
        raise ValueError("Neteisingas mentoriaus el. paštas.")
    new_photo = None
    if photo and photo[0] and photo[1]:
        if len(photo[1]) > MAX_PHOTO_BYTES:
            raise ValueError("Nuotrauka per didelė (daugiausia 2 MB).")
        ptype = photo_type(photo[1])
        if not ptype:
            raise ValueError("Nuotrauka turi būti JPG, PNG arba WebP formato.")
        new_photo = (ptype, photo[1])
    values = (name, email, (fields.get("phone") or "").strip(), (fields.get("bio") or "").strip(), (fields.get("specialties") or "").strip())
    stamp_now = now()
    with db() as c:
        if mentor_id:
            if not c.execute("SELECT 1 FROM mentors WHERE id=?", (mentor_id,)).fetchone():
                raise ValueError("Mentoriaus profilis nerastas.")
            c.execute("UPDATE mentors SET name=?,email=?,phone=?,bio=?,specialties=?,active=?,updated_at=? WHERE id=?", (*values, 1 if fields.get("active") else 0, stamp_now, mentor_id))
        else:
            mentor_id = c.execute("INSERT INTO mentors(name,email,phone,bio,specialties,active,created_at,updated_at) VALUES(?,?,?,?,?,1,?,?)", (*values, stamp_now, stamp_now)).lastrowid
        if new_photo:
            c.execute("INSERT INTO mentor_photos(mentor_id,content_type,data,updated_at) VALUES(?,?,?,?) ON CONFLICT(mentor_id) DO UPDATE SET content_type=excluded.content_type,data=excluded.data,updated_at=excluded.updated_at", (mentor_id, new_photo[0], new_photo[1], stamp_now))
        elif remove_photo:
            c.execute("DELETE FROM mentor_photos WHERE mentor_id=?", (mentor_id,))
    return mentor_id


def delete_mentor(mentor_id: int) -> None:
    with db() as c:
        c.execute("DELETE FROM mentors WHERE id=?", (mentor_id,))


def mentor_form(csrf: str, m=None) -> str:
    """The only mentor editing form (create + edit)."""
    mid = f'<input type="hidden" name="mentor_id" value="{m["id"]}">' if m else ""
    photo = f'<div class="photo-field">{avatar_html(m, True)}<div>' if m else '<div class="photo-field"><div>'
    remove = '<label class="check"><input type="checkbox" name="remove_photo" value="1"> Pašalinti nuotrauką</label>' if m and m["photo_v"] else ""
    active = f'<label class="check"><input type="checkbox" name="active" value="1"{" checked" if m["active"] else ""}> Aktyvus profilis</label>' if m else ""
    val = lambda k: esc(m[k]) if m else ""
    avg = f'{m["avg"]:.1f}' if m and m["count"] else "—"
    stats = f'<span class="muted">{m["count"]} vertinimų · {avg}/5</span>' if m else "<span></span>"
    return (f'<form method="post" action="/admin/mentor/save" class="stack" enctype="multipart/form-data">{csrf_field(csrf)}{mid}'
            f'{photo}<label>Nuotrauka (JPG, PNG arba WebP, iki 2 MB)<input type="file" name="photo" accept="image/jpeg,image/png,image/webp"></label>{remove}</div></div>'
            f'<div class="form-grid"><label>Vardas ir pavardė<input name="name" value="{val("name")}" maxlength="120" required></label>'
            f'<label>El. paštas<input name="email" type="email" value="{val("email")}" maxlength="254"></label>'
            f'<label>Telefonas<input name="phone" value="{val("phone")}" maxlength="60"></label>'
            f'<label>Kompetencijos<input name="specialties" value="{val("specialties")}" maxlength="500"></label>{active}</div>'
            f'<label>Biografija<textarea name="bio" rows="4" maxlength="5000">{val("bio")}</textarea></label>'
            f'<div class="row-end">{stats}<button class="button {"secondary small" if m else "primary"}">{"Išsaugoti" if m else "Pridėti mentorių"}</button></div></form>')


def hash_password(password: str, salt: bytes | None = None) -> str:
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, PBKDF2_ROUNDS)
    return f"pbkdf2_sha256${PBKDF2_ROUNDS}${salt.hex()}${digest.hex()}"


def check_password(password: str, encoded: str) -> bool:
    try:
        _, rounds, salt_hex, expected = encoded.split("$")
        actual = hashlib.pbkdf2_hmac("sha256", password.encode(), bytes.fromhex(salt_hex), int(rounds)).hex()
        return secrets.compare_digest(actual, expected)
    except (ValueError, TypeError):
        return False



def generate_password() -> str:
    alphabet = string.ascii_letters + string.digits + "!@#$%_-"
    while True:
        value = "".join(secrets.choice(alphabet) for _ in range(18))
        if (any(ch.islower() for ch in value) and any(ch.isupper() for ch in value)
                and any(ch.isdigit() for ch in value) and any(ch in "!@#$%_-" for ch in value)):
            return value


def invite_cipher() -> Fernet:
    configured = os.environ.get("QUESTUM_INVITE_KEY")
    if configured:
        try:
            return Fernet(configured.encode("ascii"))
        except (ValueError, UnicodeEncodeError) as exc:
            raise RuntimeError("QUESTUM_INVITE_KEY nėra galiojantis Fernet raktas.") from exc
    key_path = DB_PATH.parent / "invite.key"
    if not key_path.exists():
        key_path.parent.mkdir(parents=True, exist_ok=True)
        try:
            with key_path.open("xb") as key_file:
                key_file.write(Fernet.generate_key())
            try:
                os.chmod(key_path, 0o600)
            except OSError:
                pass
        except FileExistsError:
            pass
    return Fernet(key_path.read_bytes().strip())


def encrypt_invite_password(password: str) -> str:
    return invite_cipher().encrypt(password.encode("utf-8")).decode("ascii")


def decrypt_invite_password(value: str | None) -> str:
    if not value:
        return ""
    try:
        return invite_cipher().decrypt(value.encode("ascii")).decode("utf-8")
    except (InvalidToken, ValueError, UnicodeEncodeError, OSError, RuntimeError):
        return ""


def send_password_emails(accounts: list[tuple[int, str, str, str]]) -> dict[int, str]:
    if not accounts:
        return {}
    host = os.environ.get("QUESTUM_SMTP_HOST", "").strip()
    sender = os.environ.get("QUESTUM_SMTP_FROM", "").strip()
    if not host or not sender:
        return {account[0]: "not_configured" for account in accounts}
    try:
        port = int(os.environ.get("QUESTUM_SMTP_PORT", "587"))
        use_ssl = os.environ.get("QUESTUM_SMTP_SSL", "").lower() in ("1", "true", "yes") or port == 465
        smtp = (smtplib.SMTP_SSL(host, port, timeout=20, context=ssl.create_default_context())
                if use_ssl else smtplib.SMTP(host, port, timeout=20))
        if not use_ssl and os.environ.get("QUESTUM_SMTP_STARTTLS", "1").lower() not in ("0", "false", "no"):
            smtp.starttls(context=ssl.create_default_context())
        smtp.ehlo()
        smtp_user = os.environ.get("QUESTUM_SMTP_USER", "")
        if smtp_user:
            smtp.login(smtp_user, os.environ.get("QUESTUM_SMTP_PASSWORD", ""))
    except (OSError, smtplib.SMTPException, ValueError) as exc:
        print(f"SMTP prisijungimas nepavyko: {type(exc).__name__}")
        return {account[0]: "failed" for account in accounts}

    statuses = {}
    public_url = os.environ.get("QUESTUM_PUBLIC_URL", f"http://127.0.0.1:{PORT}").rstrip("/")
    try:
        for user_id, email, name, password in accounts:
            message = EmailMessage()
            message["Subject"] = "Questum Training paskyros prisijungimo duomenys"
            message["From"] = sender
            message["To"] = email
            message.set_content(
                f"Sveiki, {name}!\n\nSukurta jūsų Questum Training paskyra.\n"
                f"Prisijungimo adresas: {public_url}/login\nEl. paštas: {email}\n"
                f"Slaptažodis: {password}\n\nSaugokite šiuos prisijungimo duomenis."
            )
            try:
                refused = smtp.send_message(message)
                statuses[user_id] = "failed" if refused else "sent"
            except (OSError, smtplib.SMTPException) as exc:
                print(f"SMTP laiško išsiųsti nepavyko: {type(exc).__name__}")
                statuses[user_id] = "failed"
    finally:
        try:
            smtp.quit()
        except (OSError, smtplib.SMTPException):
            pass
    return statuses


def invitation_html(row, csrf: str, return_to: str) -> str:
    secret = decrypt_invite_password(row["invite_secret"])
    status = {
        "sent": "Laiškas išsiųstas.",
        "not_configured": "SMTP nesukonfigūruotas; slaptažodį galite atskleisti čia.",
        "failed": "Laiško išsiųsti nepavyko; slaptažodis išsaugotas čia.",
    }.get(row["invite_status"], "Slaptažodžio peržiūros įrašas nesukurtas.")
    if secret:
        password = f'<div class="credential-row"><input id="invite-{row["id"]}" class="credential-input" type="password" value="{esc(secret)}" readonly aria-label="Sugeneruotas slaptažodis"><button type="button" class="button secondary small" data-reveal-password="invite-{row["id"]}">Rodyti</button></div>'
    else:
        password = '<p class="muted">Slaptažodis dar nebuvo sugeneruotas šiame lange.</p>'
    return f'<div class="invite-box">{password}<span class="muted">{esc(status)}</span><form method="post" action="/admin/account/regenerate">{csrf_field(csrf)}<input type="hidden" name="user_id" value="{row["id"]}"><input type="hidden" name="return_to" value="{esc(return_to)}"><button class="link-button">Sugeneruoti ir išsiųsti naują slaptažodį</button></form></div>'


def esc(value: object) -> str:
    return html.escape(str(value or ""), quote=True)


def stamp(value: str | None) -> str:
    if not value:
        return ""
    try:
        return datetime.fromisoformat(value).astimezone().strftime("%Y-%m-%d %H:%M")
    except ValueError:
        return value


def csrf_field(token: str) -> str:
    return f'<input type="hidden" name="csrf" value="{esc(token)}">'


def select_options(rows, selected=None, value_key="id", label_key="name", include_empty=False):
    out = ['<option value="">— Nepasirinkta —</option>'] if include_empty else []
    for row in rows:
        value = row[value_key]
        label = row[label_key]
        out.append(f'<option value="{esc(value)}"{" selected" if str(value) == str(selected) else ""}>{esc(label)}</option>')
    return "".join(out)


def markdown(text: str) -> str:
    """Render a small safe subset: headings, paragraphs and http(s) links."""
    lines = text.splitlines()
    blocks, paragraph = [], []
    link_re = re.compile(r"\[([^\]]+)\]\((https?://[^\s)]+)\)")

    def inline(value: str) -> str:
        safe = esc(value)
        return link_re.sub(lambda m: f'<a href="{m.group(2)}" target="_blank" rel="noopener noreferrer">{m.group(1)}</a>', safe)

    def flush():
        if paragraph:
            blocks.append("<p>" + "<br>".join(inline(x) for x in paragraph) + "</p>")
            paragraph.clear()

    for line in lines:
        if not line.strip():
            flush()
            continue
        match = re.match(r"^(#{1,3})\s+(.+)$", line)
        if match:
            flush()
            level = len(match.group(1)) + 1
            blocks.append(f"<h{level}>{inline(match.group(2))}</h{level}>")
        else:
            paragraph.append(line)
    flush()
    return "\n".join(blocks)


def safe_url(value: str) -> bool:
    return not value or value.startswith("https://") or value.startswith("http://")


class App(BaseHTTPRequestHandler):
    server_version = "QuestumBoard/1.0"

    def log_message(self, fmt, *args):
        print(f"[{self.log_date_time_string()}] {fmt % args}")

    def send(self, body: str, status=200, content_type="text/html; charset=utf-8", headers=()):
        raw = body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
        self.send_header("Content-Security-Policy", "default-src 'self'; style-src 'self'; img-src 'self' data:; form-action 'self'; frame-ancestors 'none'; base-uri 'self'")
        for key, value in headers:
            self.send_header(key, value)
        self.end_headers()
        self.wfile.write(raw)

    def redirect(self, path: str, cookie: str | None = None):
        headers = [("Location", path), ("Cache-Control", "no-store")]
        if cookie:
            headers.append(("Set-Cookie", cookie))
        self.send("", 303, headers=headers)

    def error_page(self, message: str, code=400, user=None, csrf=""):
        self.send(self.page("Pranešimas", f'<section class="panel narrow"><h1>Pranešimas</h1><p>{esc(message)}</p><p><a class="button" href="/">Grįžti į pradžią</a></p></section>', user, csrf), code)

    def parse_form(self):
        length = min(int(self.headers.get("Content-Length", "0") or 0), 5_000_000)
        raw = self.rfile.read(length)
        ctype = self.headers.get("Content-Type", "")
        files = {}
        if ctype.startswith("multipart/form-data"):
            msg = BytesParser(policy=default).parsebytes(b"Content-Type: " + ctype.encode() + b"\r\nMIME-Version: 1.0\r\n\r\n" + raw)
            data = {}
            for part in msg.iter_parts():
                key = part.get_param("name", header="content-disposition")
                if not key:
                    continue
                content = part.get_payload(decode=True) or b""
                filename = part.get_filename()
                if filename:
                    files[key] = (filename, content)
                else:
                    data.setdefault(key, []).append(content.decode("utf-8", "replace"))
            return data, files
        parsed = parse_qs(raw.decode("utf-8", "replace"), keep_blank_values=True)
        return parsed, files

    def val(self, data, key, default=""):
        values = data.get(key, [default])
        return values[-1] if values else default

    def current(self):
        jar = SimpleCookie()
        try:
            jar.load(self.headers.get("Cookie", ""))
            raw = jar.get("qb_session").value if jar.get("qb_session") else ""
        except Exception:
            raw = ""
        if not raw:
            return None, ""
        with db() as c:
            row = c.execute("SELECT s.csrf,u.* FROM sessions s JOIN users u ON u.id=s.user_id WHERE s.token_hash=? AND s.expires_at>? AND u.active=1", (hashlib.sha256(raw.encode()).hexdigest(), int(time.time()))).fetchone()
        if row:
            return row, row["csrf"]
        return None, ""

    def has_admin(self):
        with db() as c:
            return c.execute("SELECT 1 FROM users WHERE role='admin' AND active=1 LIMIT 1").fetchone() is not None

    def new_session(self, user_id):
        token, csrf = secrets.token_urlsafe(32), secrets.token_urlsafe(24)
        expires = int(time.time()) + SESSION_HOURS * 3600
        with db() as c:
            c.execute("DELETE FROM sessions WHERE expires_at<?", (int(time.time()),))
            c.execute("INSERT INTO sessions(token_hash,user_id,csrf,expires_at) VALUES(?,?,?,?)", (hashlib.sha256(token.encode()).hexdigest(), user_id, csrf, expires))
        secure = "; Secure" if os.environ.get("QUESTUM_HTTPS", "").lower() in ("1", "true", "yes") else ""
        return f"qb_session={token}; Path=/; HttpOnly; SameSite=Lax; Max-Age={SESSION_HOURS * 3600}{secure}"

    def page(self, title, content, user=None, csrf="", active=""):
        msg = parse_qs(urlparse(self.path).query).get("msg", [""])[0]
        flash = f'<div class="flash">{esc(msg)}</div>' if msg else ""
        if user:
            nav = f'''<header class="topbar"><div class="top-inner"><a class="brand" href="/">Questum <span>TRAINING</span></a><div class="top-actions"><span class="user-name">{esc(user['name'])}</span><form method="post" action="/logout">{csrf_field(csrf)}<button class="link-button" type="submit">Atsijungti</button></form></div></div></header>
            <nav class="main-nav"><div class="nav-inner"><a class="{'current' if active == 'board' else ''}" href="/">Skelbimų lenta</a><a class="{'current' if active == 'mentors' else ''}" href="/mentors">Mentoriai</a>{'<a class="' + ('current' if active == 'admin' else '') + '" href="/admin">Administravimas</a>' if user['role'] == 'admin' else ''}</div></nav>'''
        else:
            nav = '<header class="topbar"><div class="top-inner"><a class="brand" href="/">Questum <span>TRAINING</span></a></div></header>'
        return f'''<!doctype html><html lang="lt"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{esc(title)} · Questum Training</title><link rel="stylesheet" href="/static/style.css"><script src="/static/app.js" defer></script></head><body>{nav}<main class="page-wrap">{flash}{content}</main><footer class="footer">Questum Training · Skelbimų lenta</footer></body></html>'''

    def require_login(self):
        user, csrf = self.current()
        if not user:
            self.redirect("/login?msg=" + quote("Prisijunkite, kad galėtumėte tęsti."))
            return None, ""
        return user, csrf

    def require_admin(self):
        user, csrf = self.require_login()
        if user and user["role"] != "admin":
            self.error_page("Šiai sričiai reikia administratoriaus teisių.", 403, user, csrf)
            return None, ""
        return user, csrf

    def do_GET(self):
        parsed = urlparse(self.path)
        path = unquote(parsed.path)
        if path == "/static/style.css":
            try:
                self.send((ROOT / "static" / "style.css").read_text(encoding="utf-8"), content_type="text/css; charset=utf-8", headers=(("Cache-Control", "no-cache"),))
            except OSError:
                self.send("", 404, "text/plain")
            return
        if path == "/static/app.js":
            try:
                self.send((ROOT / "static" / "app.js").read_text(encoding="utf-8"), content_type="text/javascript; charset=utf-8", headers=(("Cache-Control", "no-cache"),))
            except OSError:
                self.send("", 404, "text/plain")
            return
        if path == "/setup":
            if self.has_admin():
                self.redirect("/login")
                return
            content = '''<section class="panel narrow"><p class="eyebrow">Pirmasis paleidimas</p><h1>Sukurti administratoriaus paskyrą</h1><p>Šis vienkartinis žingsnis užrakins pradinę sąranką. Pasirinkite ilgą, unikalų slaptažodį.</p><form method="post" action="/setup" class="stack" autocomplete="off"><label>Vardas ir pavardė<input name="name" required maxlength="120" autocomplete="off"></label><label>El. paštas<input name="email" type="email" required maxlength="254" autocomplete="off"></label><label>Slaptažodis<input name="password" type="password" required minlength="12" autocomplete="off"></label><label>Pakartokite slaptažodį<input name="confirm" type="password" required minlength="12" autocomplete="off"></label><button class="button primary">Sukurti paskyrą</button></form></section>'''
            self.send(self.page("Sąranka", content))
            return
        if path == "/login":
            if not self.has_admin():
                self.redirect("/setup")
                return
            content = '''<section class="panel narrow"><p class="eyebrow">Questum Training</p><h1>Prisijungti</h1><p>Prieiga suteikiama tik administratoriaus patvirtintoms paskyroms.</p><form method="post" action="/login" class="stack"><label>El. paštas<input name="email" type="email" required autocomplete="username"></label><label>Slaptažodis<input name="password" type="password" required autocomplete="current-password"></label><button class="button primary">Prisijungti</button></form></section>'''
            self.send(self.page("Prisijungti", content))
            return
        if path == "/":
            user, csrf = self.require_login()
            if not user:
                return
            self.home(user, csrf)
            return
        if path == "/mentors":
            user, csrf = self.require_login()
            if not user:
                return
            self.mentor_list(user, csrf)
            return
        if path == "/mentor/photo":
            user, csrf = self.require_login()
            if not user:
                return
            mid = parse_qs(parsed.query).get("id", [""])[0]
            with db() as c:
                row = c.execute("SELECT p.content_type,p.data FROM mentor_photos p JOIN mentors m ON m.id=p.mentor_id WHERE p.mentor_id=? AND (m.active=1 OR ?='admin')", (mid if mid.isdigit() else 0, user["role"])).fetchone()
            if not row:
                self.send("", 404, "text/plain")
                return
            data = bytes(row["data"])
            self.send_response(200)
            self.send_header("Content-Type", row["content_type"])
            self.send_header("Content-Length", str(len(data)))
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Cache-Control", "private, max-age=86400")
            self.end_headers()
            self.wfile.write(data)
            return
        if path == "/mentor":
            user, csrf = self.require_login()
            if not user:
                return
            self.mentor_detail(user, csrf, parse_qs(parsed.query))
            return
        if path == "/admin":
            user, csrf = self.require_admin()
            if not user:
                return
            self.admin(user, csrf, parse_qs(parsed.query))
            return
        self.error_page("Puslapis nerastas.", 404)

    def home(self, user, csrf):
        with db() as c:
            total_posts = c.execute("SELECT COUNT(*) FROM announcements WHERE published=1").fetchone()[0]
            total_mentors = c.execute("SELECT COUNT(*) FROM mentors WHERE active=1").fetchone()[0]
            total_groups = c.execute("SELECT COUNT(*) FROM groups").fetchone()[0]
            groups = [r[0] for r in c.execute("SELECT group_id FROM user_groups WHERE user_id=?", (user["id"],))]
            if user["role"] == "admin":
                rows = c.execute("SELECT a.*,u.name AS author,g.name AS group_name FROM announcements a LEFT JOIN users u ON u.id=a.author_id LEFT JOIN groups g ON g.id=a.group_id WHERE a.published=1 ORDER BY a.created_at DESC").fetchall()
            else:
                scopes = ["a.visibility='all'"]
                params = []
                if groups:
                    scopes.append("(a.visibility='group' AND a.group_id IN (" + ",".join("?" for _ in groups) + "))")
                    params.extend(groups)
                where = "a.published=1 AND (" + " OR ".join("(" + x + ")" for x in scopes) + ")"
                rows = c.execute(f"SELECT a.*,u.name AS author,g.name AS group_name FROM announcements a LEFT JOIN users u ON u.id=a.author_id LEFT JOIN groups g ON g.id=a.group_id WHERE {where} ORDER BY a.created_at DESC", params).fetchall()
        cards = f'''<div class="stat-grid"><a class="stat-card" href="/"><strong>{total_posts}</strong><span>Skelbimai</span><i>↗</i></a><a class="stat-card" href="/mentors"><strong>{total_mentors}</strong><span>Aktyvūs mentoriai</span><i>↗</i></a><a class="stat-card" href="/mentors"><strong>{total_groups}</strong><span>Mokymosi grupės</span><i>↗</i></a></div>'''
        posts = []
        for row in rows:
            scope = "Visiems" if row["visibility"] == "all" else esc(row["group_name"] or "Grupė")
            attachment = f'<a class="attachment" href="{esc(row["attachment_url"])}" target="_blank" rel="noopener noreferrer">Atidaryti priedą arba nuorodą ↗</a>' if row["attachment_url"] and safe_url(row["attachment_url"]) else ""
            posts.append(f'''<article class="post panel"><div class="post-meta"><span class="badge">{scope}</span><time>{esc(stamp(row['created_at']))}</time></div><h2>{esc(row['title'])}</h2><div class="prose">{markdown(row['body'])}</div>{attachment}<div class="post-author">Atsakingas: {esc(row['author'] or 'Questum Training')}</div></article>''')
        empty = '<div class="panel empty"><h2>Skelbimų dar nėra</h2><p>Naujausi pranešimai pasirodys čia.</p></div>' if not posts else "" 
        content = f'''<section class="hero-row"><div><p class="eyebrow">Questum Training</p><h1>Skelbimų lenta</h1><p class="subtitle">Naujausia informacija ir svarbūs pranešimai jūsų mokymams.</p></div>{'<a class="button primary" href="/admin?section=announcements">+ Naujas skelbimas</a>' if user['role']=='admin' else ''}</section>{cards}<section class="content-section"><div class="section-heading"><h2>Naujausi skelbimai</h2><span class="muted">{len(posts)} pranešimai</span></div>{''.join(posts)}{empty}</section>'''
        self.send(self.page("Skelbimų lenta", content, user, csrf, "board"))

    def mentor_list(self, user, csrf):
        query = parse_qs(urlparse(self.path).query).get("q", [""])[0].strip()
        with db() as c:
            if query:
                rows = c.execute("SELECT m.*,(SELECT updated_at FROM mentor_photos WHERE mentor_id=m.id) AS photo_v,COALESCE(AVG(r.stars),0) AS avg,COUNT(r.id) AS count FROM mentors m LEFT JOIN ratings r ON r.mentor_id=m.id WHERE m.active=1 AND (m.name LIKE ? OR m.specialties LIKE ?) GROUP BY m.id ORDER BY m.name", (f"%{query}%", f"%{query}%")).fetchall()
            else:
                rows = c.execute("SELECT m.*,(SELECT updated_at FROM mentor_photos WHERE mentor_id=m.id) AS photo_v,COALESCE(AVG(r.stars),0) AS avg,COUNT(r.id) AS count FROM mentors m LEFT JOIN ratings r ON r.mentor_id=m.id WHERE m.active=1 GROUP BY m.id ORDER BY m.name").fetchall()
        cards = []
        for r in rows:
            stars = f"{r['avg']:.1f}" if r["count"] else "—"
            cards.append(f'''<a class="mentor-card panel" href="/mentor?id={r['id']}">{avatar_html(r)}<div class="mentor-card-copy"><h2>{esc(r['name'])}</h2><p>{esc(r['specialties'] or 'Mentorius · Questum Training')}</p><div class="rating-line"><span class="stars">★</span><strong>{stars}</strong><span class="muted">({r['count']} vert.)</span></div></div><span class="arrow">↗</span></a>''')
        empty = '<div class="panel empty"><h2>Mentorių dar nėra</h2><p>Administratorius gali sukurti profilius administravimo skydelyje.</p></div>' if not cards else ""
        content = f'''<section class="hero-row"><div><p class="eyebrow">Katalogas</p><h1>Mentoriai</h1><p class="subtitle">Susipažinkite su mentoriais, jų patirtimi ir kompetencijomis.</p></div>{'<a class="button primary" href="/admin?section=mentors">+ Pridėti mentorių</a>' if user['role']=='admin' else ''}</section><form class="search-row" method="get"><input name="q" value="{esc(query)}" placeholder="Ieškoti mentoriaus ar kompetencijos"><button class="button secondary">Ieškoti</button>{'<a href="/mentors">Išvalyti</a>' if query else ''}</form><div class="mentor-grid">{''.join(cards)}</div>{empty}'''
        self.send(self.page("Mentoriai", content, user, csrf, "mentors"))

    def mentor_detail(self, user, csrf, query):
        mid = query.get("id", [""])[0]
        with db() as c:
            mentor = c.execute("SELECT m.*,(SELECT updated_at FROM mentor_photos WHERE mentor_id=m.id) AS photo_v,COALESCE(AVG(r.stars),0) AS avg,COUNT(r.id) AS count FROM mentors m LEFT JOIN ratings r ON r.mentor_id=m.id WHERE m.id=? AND (m.active=1 OR ?='admin') GROUP BY m.id", (mid, user["role"])).fetchone()
            if not mentor:
                self.error_page("Mentorius nerastas.", 404, user, csrf)
                return
            own = c.execute("SELECT * FROM ratings WHERE mentor_id=? AND user_id=?", (mid, user["id"])).fetchone()
            comments = c.execute("SELECT stars,comment,created_at FROM ratings WHERE mentor_id=? AND comment<>'' AND comment_hidden=0 ORDER BY updated_at DESC", (mid,)).fetchall()
        stats = f"{mentor['avg']:.1f}" if mentor["count"] else "—"
        can_rate = user["role"] == "participant"
        rating_form = ""
        if can_rate:
            existing = own["stars"] if own else 0
            radios = "".join(f'<label class="star-choice"><input type="radio" name="stars" value="{n}" required{" checked" if n == existing else ""}><span>{n}</span></label>' for n in range(1, 6))
            rating_form = f'''<section class="panel"><h2>{'Atnaujinti savo vertinimą' if own else 'Įvertinti mentorių'}</h2><form method="post" action="/rating/save" class="stack">{csrf_field(csrf)}<input type="hidden" name="mentor_id" value="{mentor['id']}"><fieldset><legend>Jūsų įvertinimas</legend><div class="star-picker">{radios}</div></fieldset><label>Komentaras (neprivalomas)<textarea name="comment" rows="4" maxlength="2000" placeholder="Pasidalinkite patirtimi…">{esc(own['comment'] if own else '')}</textarea></label><button class="button primary">{ 'Atnaujinti vertinimą' if own else 'Pateikti vertinimą'}</button></form>{f'<form method="post" action="/rating/delete" class="inline-form">{csrf_field(csrf)}<input type="hidden" name="mentor_id" value="{mentor["id"]}"><button class="link-button danger">Pašalinti mano vertinimą</button></form>' if own else ''}</section>'''
        elif user["role"] != "admin":
            rating_form = '<section class="panel info-note">Vertinimus gali pateikti prisijungę DaVinci dalyviai.</section>'
        contact = f'<div class="contact-list"><div><span>El. paštas</span><a href="mailto:{esc(mentor["email"])}">{esc(mentor["email"] or "—")}</a></div><div><span>Telefonas</span><a href="tel:{esc(mentor["phone"])}">{esc(mentor["phone"] or "—")}</a></div></div>'
        review_html = "".join(f'<article class="review"><div class="review-head"><span class="stars">{"★" * r["stars"]}{"☆" * (5-r["stars"])}</span><time>{esc(stamp(r["created_at"]))}</time></div><p>{esc(r["comment"])}</p><span class="muted">Dalyvio tapatybė nerodoma</span></article>' for r in comments)
        content = f'''<p class="breadcrumb"><a href="/mentors">← Visi mentoriai</a></p><section class="mentor-profile panel">{avatar_html(mentor, True)}<div class="profile-main"><p class="eyebrow">Mentorius</p><h1>{esc(mentor['name'])}</h1><p class="profile-specialties">{esc(mentor['specialties'] or 'Questum Training')}</p><div class="rating-line"><span class="stars">★</span><strong>{stats}</strong><span class="muted">iš 5 · {mentor['count']} vertinimų</span></div></div></section><div class="detail-grid"><div class="stack"><section class="panel"><h2>Apie mentorių</h2><div class="prose">{markdown(mentor['bio'] or 'Profilio aprašymas dar nepridėtas.')}</div><h3>Patirtis ir kompetencijos</h3><div class="prose">{markdown(mentor['specialties'] or 'Informacija dar nepridėta.')}</div></section><section class="panel"><h2>Dalyvių atsiliepimai</h2>{review_html or '<p class="muted">Paskelbtų komentarų dar nėra.</p>'}</section></div><aside class="stack">{rating_form}<section class="panel"><h2>Kontaktai</h2>{contact}</section></aside></div>'''
        self.send(self.page(mentor["name"], content, user, csrf, "mentors"))

    def admin(self, user, csrf, query):
        section = query.get("section", ["users"])[0]
        if section not in ("users", "announcements", "mentors", "reviews"):
            section = "users"
        sections = [("users", "Vartotojai"), ("mentors", "Mentoriai"), ("announcements", "Skelbimai"), ("reviews", "Vertinimai")]
        tabs = ''.join(f'<a class="tab{" active" if section == key else ""}" href="/admin?section={key}">{label}</a>' for key, label in sections)
        with db() as c:
            counts = {key: c.execute(sql).fetchone()[0] for key, sql in {
                "users": "SELECT COUNT(*) FROM users WHERE active=1", "groups": "SELECT COUNT(*) FROM groups",
                "announcements": "SELECT COUNT(*) FROM announcements", "mentors": "SELECT COUNT(*) FROM mentors WHERE active=1",
                "reviews": "SELECT COUNT(*) FROM ratings"}.items()}
        body = self.admin_section(section, user, csrf)
        content = f'''<section class="hero-row"><div><p class="eyebrow">Valdymo aplinka</p><h1>Administravimas</h1><p class="subtitle">Paskyros ir profiliai vienoje vietoje; grupės, skelbimai ir vertinimai.</p></div></section><div class="stat-grid admin-stats">{''.join(f'<div class="stat-card"><strong>{counts[k]}</strong><span>{label}</span></div>' for k,label in (("users","Vartotojai"),("mentors","Mentoriai"),("announcements","Skelbimai"),("reviews","Vertinimai")))}</div><div class="tabs">{tabs}</div>{body}'''
        self.send(self.page("Administravimas", content, user, csrf, "admin"))

    def admin_section_legacy(self, section, user, csrf):
        with db() as c:
            groups = c.execute("SELECT * FROM groups ORDER BY name").fetchall()
            if section == "announcements":
                rows = c.execute("SELECT a.*,g.name AS group_name FROM announcements a LEFT JOIN groups g ON g.id=a.group_id ORDER BY a.created_at DESC").fetchall()
                cards = []
                for r in rows:
                    vis = ''.join(f'<option value="{v}"{" selected" if r["visibility"]==v else ""}>{label}</option>' for v,label in (("all","Visiems dalyviams"),("group","Pasirinkta grupė")))
                    group_opts = ''.join(f'<option value="{g["id"]}"{" selected" if str(r["group_id"] or "")==str(g["id"]) else ""}>{esc(g["name"])}</option>' for g in groups)
                    cards.append(f'''<article class="manage-card"><form method="post" action="/admin/announcement/save" class="stack">{csrf_field(csrf)}<input type="hidden" name="announcement_id" value="{r['id']}"><div class="form-grid"><label>Pavadinimas<input name="title" value="{esc(r['title'])}" required maxlength="200"></label><label>Matomumas<select name="visibility">{vis}</select></label><label>Grupė<select name="group_id"><option value="">— Pasirinkti grupę —</option>{group_opts}</select></label><label>Nuoroda / priedas<input name="attachment_url" type="url" value="{esc(r['attachment_url'])}" placeholder="https://…"></label></div><label>Tekstas <span class="muted">(antraštėms naudokite ##, nuorodoms [tekstas](https://...))</span><textarea name="body" rows="6" required>{esc(r['body'])}</textarea></label><div class="row-end"><label class="check"><input type="checkbox" name="published" value="1"{' checked' if r['published'] else ''}> Paskelbtas</label><span class="muted">{esc(stamp(r['updated_at']))} · {esc(r['group_name'] or ('Visiems' if r['visibility']=='all' else 'Mentoriams'))}</span><button class="button secondary">Išsaugoti</button></div></form><form method="post" action="/admin/announcement/delete" class="delete-form" data-confirm="Pašalinti šį skelbimą? Šis veiksmas negrįžtamas.">{csrf_field(csrf)}<input type="hidden" name="announcement_id" value="{r['id']}"><button class="link-button danger">Pašalinti skelbimą</button></form></article>''')
                new_vis = '<option value="all">Visiems dalyviams</option><option value="group">Pasirinkta grupė</option>'
                group_opts = ''.join(f'<option value="{g["id"]}">{esc(g["name"])}</option>' for g in groups)
                return f'''<section class="admin-section"><div class="section-heading"><h2>Skelbimai</h2><span class="muted">Naujausi rodomi pirmiausia</span></div><div class="manage-grid">{''.join(cards) or '<p class="muted">Skelbimų dar nėra.</p>'}</div><section class="panel"><h3>Sukurti skelbimą</h3><form method="post" action="/admin/announcement/save" class="stack">{csrf_field(csrf)}<div class="form-grid"><label>Pavadinimas<input name="title" required maxlength="200"></label><label>Matomumas<select name="visibility">{new_vis}</select></label><label>Grupė<select name="group_id"><option value="">— Pasirinkti grupę —</option>{group_opts}</select></label><label>Nuoroda / priedas<input name="attachment_url" type="url" placeholder="https://…"></label></div><label>Tekstas<textarea name="body" rows="6" required placeholder="Parašykite skelbimo tekstą…"></textarea></label><label class="check"><input type="checkbox" name="published" value="1"> Paskelbti iš karto</label><button class="button primary">Sukurti skelbimą</button></form></section></section>'''
            if section == "reviews":
                rows = c.execute("SELECT r.*,m.name AS mentor_name,u.name AS user_name,u.email AS user_email FROM ratings r JOIN mentors m ON m.id=r.mentor_id JOIN users u ON u.id=r.user_id ORDER BY r.updated_at DESC").fetchall()
                cards=[]
                for r in rows:
                    cards.append(f'''<article class="manage-card review-admin"><div><h3>{esc(r['mentor_name'])} <span class="stars">{"★"*r['stars']}{"☆"*(5-r['stars'])}</span></h3><p>{esc(r['comment'] or 'Komentaro nėra.')}</p><p class="muted">Pateikė {esc(r['user_name'])} · {esc(r['user_email'])} · {esc(stamp(r['created_at']))} · atnaujinta {esc(stamp(r['updated_at']))}</p></div><form method="post" action="/admin/review/moderate" class="row-end">{csrf_field(csrf)}<input type="hidden" name="rating_id" value="{r['id']}"><label class="check"><input type="checkbox" name="hidden" value="1"{' checked' if r['comment_hidden'] else ''}> Slėpti komentarą</label><button class="button secondary">Išsaugoti</button></form></article>''')
                return f'''<section class="admin-section"><div class="section-heading"><h2>Vertinimai ir komentarai</h2><span class="muted">Dalyvių vardai matomi tik administratoriams.</span></div><div class="manage-grid">{''.join(cards) or '<div class="panel empty"><p>Vertinimų dar nėra.</p></div>'}</div></section>'''
        return ""


    def admin_section(self, section, user, csrf):
        if section in ("announcements", "reviews"):
            return self.admin_section_legacy(section, user, csrf)
        with db() as c:
            groups = c.execute("SELECT * FROM groups ORDER BY name").fetchall()
            if section == "users":
                rows = c.execute("SELECT u.*,GROUP_CONCAT(ug.group_id) AS group_ids FROM users u LEFT JOIN user_groups ug ON ug.user_id=u.id GROUP BY u.id ORDER BY u.name").fetchall()
                group_cards = []
                for group in groups:
                    members = c.execute("SELECT COUNT(*) FROM user_groups WHERE group_id=?", (group["id"],)).fetchone()[0]
                    group_cards.append(f'''<div class="group-row"><form method="post" action="/admin/group/save" class="inline-fields">{csrf_field(csrf)}<input type="hidden" name="group_id" value="{group["id"]}"><label>Grupė<input name="name" value="{esc(group["name"])}" maxlength="100" required></label><span class="muted">{members} vart.</span><button class="button secondary small">Išsaugoti</button></form><form method="post" action="/admin/group/delete" data-confirm="Pašalinti grupę? Dalyvių priskyrimai ir grupės skelbimų matomumas bus panaikinti.">{csrf_field(csrf)}<input type="hidden" name="group_id" value="{group["id"]}"><button class="link-button danger">Pašalinti</button></form></div>''')
                cards = []
                for row in rows:
                    group_ids = set((row["group_ids"] or "").split(","))
                    group_options = "".join(f'<option value="{g["id"]}"{" selected" if str(g["id"]) in group_ids else ""}>{esc(g["name"])}</option>' for g in groups)
                    role_options = "".join(f'<option value="{role}"{" selected" if row["role"] == role else ""}>{label}</option>' for role,label in (("participant","Dalyvis"),("admin","Administratorius")))
                    cards.append(f'''<article class="manage-card"><form method="post" action="/admin/user/save" class="stack">{csrf_field(csrf)}<input type="hidden" name="user_id" value="{row["id"]}"><div class="form-grid"><label>Vardas<input name="name" value="{esc(row["name"])}" maxlength="120" required></label><label>El. paštas<input name="email" type="email" value="{esc(row["email"])}" maxlength="254" required></label><label>Rolė<select name="role">{role_options}</select></label><label>Grupės<select name="group_ids" multiple size="2">{group_options}</select></label></div><div class="row-end"><label class="check"><input type="checkbox" name="active" value="1"{" checked" if row["active"] else ""}> Aktyvi paskyra</label><span class="muted">Sukurta {esc(stamp(row["created_at"]))}</span><button class="button secondary small">Išsaugoti</button></div></form>{invitation_html(row,csrf,"users")}<form method="post" action="/admin/user/delete" class="delete-form" data-confirm="Pašalinti vartotoją ir jo vertinimus? Šio veiksmo atkurti nebus galima.">{csrf_field(csrf)}<input type="hidden" name="user_id" value="{row["id"]}"><button class="link-button danger">Pašalinti vartotoją</button></form></article>''')
                group_options = "".join(f'<option value="{g["id"]}">{esc(g["name"])}</option>' for g in groups)
                smtp_ready = bool(os.environ.get("QUESTUM_SMTP_HOST") and os.environ.get("QUESTUM_SMTP_FROM"))
                mail_note = "El. laiškų siuntimas paruoštas." if smtp_ready else "El. pašto siuntimas neįjungtas: nustatykite SMTP parametrus README instrukcijoje. Sugeneruotą slaptažodį vis tiek galėsite atskleisti čia."
                return f'''<section class="admin-section"><div class="section-heading"><div><h2>Vartotojai</h2><p class="muted">Pridėkite dalyvius čia. Mentoriaus paskyra sukuriama kartu su jo profiliu, skiltyje „Mentoriai“.</p></div></div><div class="info-note panel">{esc(mail_note)}</div><div class="manage-grid">{''.join(cards) or '<div class="panel empty"><p>Vartotojų dar nėra.</p></div>'}</div><section class="panel"><h3>Pridėti vartotoją</h3><form method="post" action="/admin/user/save" class="stack">{csrf_field(csrf)}<div class="form-grid"><label>Vardas<input name="name" maxlength="120" required></label><label>El. paštas<input name="email" type="email" maxlength="254" required></label><label>Rolė<select name="role"><option value="participant">DaVinci dalyvis</option><option value="admin">Administratorius</option></select></label><label>Grupė<select name="group_ids"><option value="">— Be grupės —</option>{group_options}</select></label></div><p class="muted">Slaptažodis bus sugeneruotas automatiškai.</p><button class="button primary">Sukurti paskyrą</button></form></section><section class="panel"><h3>Importuoti dalyvius</h3><p class="muted">CSV stulpeliai: <code>email,name,groups</code>. Grupes atskirkite kabliataškiu. Kiekvienas naujas dalyvis gaus atskirą automatiškai sugeneruotą slaptažodį.</p><form method="post" action="/admin/users/import" enctype="multipart/form-data" class="inline-fields">{csrf_field(csrf)}<label>CSV failas<input type="file" name="csv_file" accept=".csv,text/csv" required></label><button class="button secondary">Importuoti ir siųsti prisijungimus</button></form></section><details class="panel group-settings"><summary>Grupių valdymas</summary><div class="group-list">{''.join(group_cards) or '<p class="muted">Grupių dar nėra.</p>'}</div><form method="post" action="/admin/group/save" class="inline-fields group-create">{csrf_field(csrf)}<label>Nauja grupė<input name="name" maxlength="100" placeholder="Pvz., DaVinci 2026" required></label><button class="button secondary">Sukurti grupę</button></form></details></section>'''

            if section == "mentors":
                rows = c.execute("SELECT m.*,(SELECT updated_at FROM mentor_photos WHERE mentor_id=m.id) AS photo_v,COALESCE(AVG(r.stars),0) AS avg,COUNT(r.id) AS count FROM mentors m LEFT JOIN ratings r ON r.mentor_id=m.id GROUP BY m.id ORDER BY m.name").fetchall()
                cards = [f'''<article class="manage-card">{mentor_form(csrf, row)}<form method="post" action="/admin/mentor/delete" class="delete-form" data-confirm="Pašalinti mentoriaus profilį? Susieti vertinimai bus ištrinti negrįžtamai.">{csrf_field(csrf)}<input type="hidden" name="mentor_id" value="{row["id"]}"><button class="link-button danger">Pašalinti mentorių</button></form></article>''' for row in rows]
                return f'''<section class="admin-section"><div class="section-heading"><div><h2>Mentoriai</h2><p class="muted">Mentoriai yra tik profilių įrašai (be prisijungimo). Visi duomenys tvarkomi čia.</p></div></div><div class="manage-grid">{''.join(cards) or '<div class="panel empty"><p>Mentorių dar nėra.</p></div>'}</div><section class="panel"><h3>Pridėti mentorių</h3>{mentor_form(csrf)}</section></section>'''
        return ""

    def do_POST(self):
        path = urlparse(self.path).path
        data, files = self.parse_form()
        user, csrf = self.current()
        if path == "/setup":
            if self.has_admin():
                self.redirect("/login")
                return
            name, email = self.val(data, "name").strip(), self.val(data, "email").strip().lower()
            password, confirm = self.val(data, "password"), self.val(data, "confirm")
            if not name or "@" not in email or len(password) < 12 or password != confirm:
                self.redirect("/setup?msg=" + quote("Patikrinkite vardą, el. paštą ir slaptažodį (mažiausiai 12 simbolių)."))
                return
            try:
                already_configured = False
                admin_id = None
                with db() as c:
                    c.execute("BEGIN IMMEDIATE")
                    if c.execute("SELECT 1 FROM users WHERE role='admin' AND active=1 LIMIT 1").fetchone():
                        already_configured = True
                    else:
                        cur = c.execute("INSERT INTO users(name,email,role,password_hash,active,created_at,updated_at) VALUES(?,?,'admin',?,1,?,?)", (name,email,hash_password(password),now(),now()))
                        admin_id = cur.lastrowid
                        c.execute("INSERT OR IGNORE INTO groups(name,created_at) VALUES('DaVinci',?)", (now(),))
                        c.execute("INSERT INTO announcements(title,body,author_id,visibility,published,created_at,updated_at) VALUES(?,?,?,'all',1,?,?)", ("Sveiki atvykę į Questum Training", "Čia rasite naujausius mokymų pranešimus. Administratorius gali skelbimų lentos turinį, grupes ir mentorių profilius tvarkyti administravimo skydelyje.", admin_id, now(), now()))
                if already_configured:
                    self.redirect("/login?msg=" + quote("Pradinė sąranka jau baigta."))
                else:
                    self.redirect("/admin", self.new_session(admin_id))
            except sqlite3.IntegrityError:
                self.redirect("/setup?msg=" + quote("Toks el. pašto adresas jau naudojamas."))
            return
        if path == "/login":
            email, password = self.val(data, "email").strip().lower(), self.val(data, "password")
            with db() as c:
                row = c.execute("SELECT * FROM users WHERE email=? AND active=1 AND role IN ('admin','participant')", (email,)).fetchone()
            if not row or not check_password(password, row["password_hash"]):
                self.redirect("/login?msg=" + quote("El. paštas arba slaptažodis neteisingas, arba paskyra neaktyvi."))
            else:
                self.redirect("/", self.new_session(row["id"]))
            return
        if not user:
            self.redirect("/login?msg=" + quote("Prisijunkite, kad galėtumėte tęsti."))
            return
        if self.val(data, "csrf") != csrf:
            self.error_page("Saugumo patikra nepavyko. Atnaujinkite puslapį ir bandykite dar kartą.", 403, user, csrf)
            return
        if path == "/logout":
            jar = SimpleCookie()
            jar.load(self.headers.get("Cookie", ""))
            raw = jar.get("qb_session").value if jar.get("qb_session") else ""
            with db() as c:
                c.execute("DELETE FROM sessions WHERE token_hash=?", (hashlib.sha256(raw.encode()).hexdigest(),))
            self.redirect("/login", "qb_session=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0")
            return
        if path.startswith("/admin/") and user["role"] != "admin":
            self.error_page("Šiam veiksmui reikia administratoriaus teisių.", 403, user, csrf)
            return
        try:
            self.post_action(path, data, files, user, csrf)
        except (sqlite3.IntegrityError, ValueError, RuntimeError) as exc:
            message = str(exc) or "Nepavyko išsaugoti pakeitimų."
            self.redirect(self.back_path(path, data) + "?msg=" + quote(message[:220]))

    def back_path(self, path, data):
        if path.startswith("/admin/"):
            section = {"/admin/group": "groups", "/admin/user": "users", "/admin/users": "users", "/admin/announcement": "announcements", "/admin/mentor": "mentors", "/admin/review": "reviews"}
            prefix = next((v for k,v in section.items() if path.startswith(k)), "overview")
            return "/admin?section=" + prefix
        mid = self.val(data, "mentor_id")
        return "/mentor?id=" + quote(mid) if mid else "/"


    def account_action(self, path, data, files, user, csrf):
        if path == "/admin/user/save":
            uid = self.val(data,"user_id")
            name = self.val(data,"name").strip()
            email = self.val(data,"email").strip().lower()
            role = self.val(data,"role")
            group_ids = data.get("group_ids", [])
            if not name or "@" not in email or role not in ("participant","admin"):
                raise ValueError("Patikrinkite vardą, el. paštą ir rolę.")
            password = ""
            account_id = None
            with db() as c:
                if uid:
                    uid = int(uid)
                    old = c.execute("SELECT role FROM users WHERE id=?", (uid,)).fetchone()
                    if not old:
                        raise ValueError("Paskyra nerasta.")
                    active = 1 if self.val(data,"active") == "1" else 0
                    if uid == user["id"] and (not active or role != "admin"):
                        raise ValueError("Negalite išjungti arba pakeisti savo administratoriaus paskyros.")
                    if old["role"] == "admin" and (not active or role != "admin"):
                        others = c.execute("SELECT COUNT(*) FROM users WHERE role='admin' AND active=1 AND id<>?", (uid,)).fetchone()[0]
                        if not others:
                            raise ValueError("Turi likti bent vienas aktyvus administratorius.")
                    c.execute("UPDATE users SET name=?,email=?,role=?,active=?,updated_at=? WHERE id=?", (name,email,role,active,now(),uid))
                    c.execute("DELETE FROM user_groups WHERE user_id=?", (uid,))
                    account_id = uid
                else:
                    password = generate_password()
                    c.execute(
                        "INSERT INTO users(name,email,role,password_hash,active,created_at,updated_at,invite_secret,invite_status,invite_updated_at) VALUES(?,?,?,?,1,?,?,?,?,?)",
                        (name,email,role,hash_password(password),now(),now(),encrypt_invite_password(password),"not_configured",now()),
                    )
                    account_id = c.execute("SELECT id FROM users WHERE email=?", (email,)).fetchone()["id"]
                for group_id in group_ids:
                    if group_id:
                        c.execute("INSERT OR IGNORE INTO user_groups(user_id,group_id) VALUES(?,?)", (account_id,int(group_id)))
            if password:
                status = send_password_emails([(account_id,email,name,password)]).get(account_id,"failed")
                with db() as c:
                    c.execute("UPDATE users SET invite_status=?,invite_updated_at=? WHERE id=?", (status,now(),account_id))
                message = "Paskyra sukurta. " + ("Slaptažodis išsiųstas el. paštu." if status == "sent" else "Slaptažodį galite atskleisti paskyros kortelėje.")
            else:
                message = "Pakeitimai išsaugoti."
            self.redirect("/admin?section=users&msg=" + quote(message))
            return

        if path == "/admin/users/import":
            filename, raw = files.get("csv_file", ("",b""))
            if not filename.lower().endswith(".csv") or not raw:
                raise ValueError("Pasirinkite CSV failą.")
            reader = csv.DictReader(io.StringIO(raw.decode("utf-8-sig")))
            if not reader.fieldnames or "email" not in [column.lower() for column in reader.fieldnames]:
                raise ValueError("CSV faile turi būti email stulpelis.")
            headers = {column.lower():column for column in reader.fieldnames}
            accounts, added, duplicates = [], 0, 0
            with db() as c:
                known_groups = {row["name"].lower():row["id"] for row in c.execute("SELECT * FROM groups")}
                for row in reader:
                    email = (row.get(headers.get("email","email")) or "").strip().lower()
                    if not email or "@" not in email:
                        continue
                    name = (row.get(headers.get("name","name")) or email.split("@")[0]).strip()
                    if c.execute("SELECT 1 FROM users WHERE email=?", (email,)).fetchone():
                        duplicates += 1
                        continue
                    password = generate_password()
                    cur = c.execute(
                        "INSERT INTO users(name,email,role,password_hash,active,created_at,updated_at,invite_secret,invite_status,invite_updated_at) VALUES(?,?,'participant',?,1,?,?,?,?,?)",
                        (name,email,hash_password(password),now(),now(),encrypt_invite_password(password),"not_configured",now()),
                    )
                    account_id = cur.lastrowid
                    added += 1
                    accounts.append((account_id,email,name,password))
                    groups_text = row.get(headers.get("groups","groups"),"") or ""
                    for group_name in re.split(r"[;|]",groups_text):
                        group_id = known_groups.get(group_name.strip().lower())
                        if group_id:
                            c.execute("INSERT OR IGNORE INTO user_groups(user_id,group_id) VALUES(?,?)", (account_id,group_id))
            statuses = send_password_emails(accounts)
            if statuses:
                with db() as c:
                    for account_id,status in statuses.items():
                        c.execute("UPDATE users SET invite_status=?,invite_updated_at=? WHERE id=?", (status,now(),account_id))
            sent = sum(status == "sent" for status in statuses.values())
            not_sent = added - sent
            message = f"Pridėta {added} dalyvių; el. paštu išsiųsta {sent}; neišsiųsta {not_sent}; dublikatų praleista {duplicates}."
            self.redirect("/admin?section=users&msg=" + quote(message))
            return

        if path == "/admin/mentor/save":
            mid = self.val(data, "mentor_id")
            save_mentor({k: self.val(data, k) for k in ("name", "email", "phone", "bio", "specialties", "active")},
                        files.get("photo"), self.val(data, "remove_photo") == "1", int(mid) if mid.isdigit() else None)
            self.redirect("/admin?section=mentors&msg=" + quote("Mentoriaus profilis išsaugotas."))
            return

        if path == "/admin/mentor/delete":
            mid = self.val(data, "mentor_id")
            if mid.isdigit():
                delete_mentor(int(mid))
            self.redirect("/admin?section=mentors&msg=" + quote("Mentoriaus profilis pašalintas."))
            return

        if path == "/admin/account/regenerate":
            account_id = int(self.val(data,"user_id") or 0)
            return_to = self.val(data,"return_to")
            if return_to != "users":
                return_to = "users"
            with db() as c:
                row = c.execute("SELECT name,email,role,active FROM users WHERE id=?", (account_id,)).fetchone()
                if not row:
                    raise ValueError("Paskyra nerasta.")
                if not row["active"]:
                    raise ValueError("Pirmiausia aktyvinkite šią paskyrą.")
                password = generate_password()
                c.execute("UPDATE users SET password_hash=?,invite_secret=?,invite_status='not_configured',invite_updated_at=?,updated_at=? WHERE id=?", (hash_password(password),encrypt_invite_password(password),now(),now(),account_id))
                send_account = (account_id,row["email"],row["name"],password)
            status = send_password_emails([send_account]).get(account_id,"failed")
            with db() as c:
                c.execute("UPDATE users SET invite_status=?,invite_updated_at=? WHERE id=?", (status,now(),account_id))
            message = "Naujas slaptažodis išsiųstas el. paštu." if status == "sent" else "Naujas slaptažodis sugeneruotas ir užmaskuotas paskyros kortelėje."
            self.redirect("/admin?section=" + return_to + "&msg=" + quote(message))
            return


    def post_action(self, path, data, files, user, csrf):
        if path in ("/admin/user/save", "/admin/users/import", "/admin/mentor/save", "/admin/mentor/delete", "/admin/account/regenerate"):
            return self.account_action(path, data, files, user, csrf)
        if path == "/rating/save":
            if user["role"] != "participant":
                self.error_page("Vertinti gali tik patvirtinti DaVinci dalyviai.", 403, user, csrf)
                return
            mid = int(self.val(data, "mentor_id") or 0)
            stars = int(self.val(data, "stars") or 0)
            comment = self.val(data, "comment").strip()
            if stars < 1 or stars > 5 or len(comment) > 2000:
                raise ValueError("Pasirinkite 1–5 žvaigždutes; komentaras gali būti iki 2 000 simbolių.")
            with db() as c:
                mentor = c.execute("SELECT active FROM mentors WHERE id=?", (mid,)).fetchone()
                if not mentor or not mentor["active"]:
                    raise ValueError("Šio mentoriaus įvertinti negalima.")
                prior = c.execute("SELECT id,created_at FROM ratings WHERE mentor_id=? AND user_id=?", (mid,user["id"])).fetchone()
                timestamp = now()
                if prior:
                    c.execute("UPDATE ratings SET stars=?,comment=?,updated_at=? WHERE id=?", (stars,comment,timestamp,prior["id"]))
                else:
                    c.execute("INSERT INTO ratings(mentor_id,user_id,stars,comment,created_at,updated_at) VALUES(?,?,?,?,?,?)", (mid,user["id"],stars,comment,timestamp,timestamp))
            self.redirect(f"/mentor?id={mid}&msg=" + quote("Vertinimas išsaugotas."))
            return
        if path == "/rating/delete":
            mid = int(self.val(data, "mentor_id") or 0)
            with db() as c:
                c.execute("DELETE FROM ratings WHERE mentor_id=? AND user_id=?", (mid,user["id"]))
            self.redirect(f"/mentor?id={mid}&msg=" + quote("Vertinimas pašalintas."))
            return
        if path == "/admin/group/save":
            name = self.val(data,"name").strip()
            if not name: raise ValueError("Įrašykite grupės pavadinimą.")
            gid = self.val(data,"group_id")
            with db() as c:
                if gid: c.execute("UPDATE groups SET name=? WHERE id=?", (name,int(gid)))
                else: c.execute("INSERT INTO groups(name,created_at) VALUES(?,?)", (name,now()))
            self.redirect("/admin?section=groups&msg=" + quote("Grupė išsaugota.")); return
        if path == "/admin/group/delete":
            with db() as c: c.execute("DELETE FROM groups WHERE id=?", (int(self.val(data,"group_id") or 0),))
            self.redirect("/admin?section=groups&msg=" + quote("Grupė pašalinta.")); return
        if path == "/admin/user/delete":
            uid=int(self.val(data,"user_id") or 0)
            if uid == user["id"]: raise ValueError("Negalite pašalinti savo paskyros.")
            with db() as c:
                row=c.execute("SELECT role FROM users WHERE id=?",(uid,)).fetchone()
                if row and row["role"]=="admin" and c.execute("SELECT COUNT(*) FROM users WHERE role='admin' AND active=1 AND id<>?",(uid,)).fetchone()[0] == 0:
                    raise ValueError("Turi likti bent vienas aktyvus administratorius.")
                c.execute("DELETE FROM users WHERE id=?",(uid,))
            self.redirect("/admin?section=users&msg=" + quote("Vartotojas pašalintas.")); return
        if path == "/admin/announcement/save":
            aid=self.val(data,"announcement_id")
            title=self.val(data,"title").strip(); body=self.val(data,"body").strip()
            visibility=self.val(data,"visibility")
            gid=self.val(data,"group_id") or None
            attachment=self.val(data,"attachment_url").strip()
            if not title or not body or visibility not in ("all","group"): raise ValueError("Patikrinkite skelbimo pavadinimą, tekstą ir matomumą.")
            if visibility=="group" and not gid: raise ValueError("Pasirinkite grupę šiam skelbimui.")
            if attachment and not safe_url(attachment): raise ValueError("Nuoroda turi prasidėti http:// arba https://.")
            timestamp=now(); published=1 if self.val(data,"published")=="1" else 0
            with db() as c:
                if aid: c.execute("UPDATE announcements SET title=?,body=?,visibility=?,group_id=?,attachment_url=?,published=?,updated_at=? WHERE id=?",(title,body,visibility,gid if visibility=="group" else None,attachment,published,timestamp,int(aid)))
                else: c.execute("INSERT INTO announcements(title,body,author_id,visibility,group_id,attachment_url,published,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?)",(title,body,user["id"],visibility,gid if visibility=="group" else None,attachment,published,timestamp,timestamp))
            self.redirect("/admin?section=announcements&msg=" + quote("Skelbimas išsaugotas.")); return
        if path == "/admin/announcement/delete":
            with db() as c: c.execute("DELETE FROM announcements WHERE id=?",(int(self.val(data,"announcement_id") or 0),))
            self.redirect("/admin?section=announcements&msg=" + quote("Skelbimas pašalintas.")); return
        if path == "/admin/review/moderate":
            with db() as c: c.execute("UPDATE ratings SET comment_hidden=?,updated_at=? WHERE id=?",(1 if self.val(data,"hidden")=="1" else 0,now(),int(self.val(data,"rating_id") or 0)))
            self.redirect("/admin?section=reviews&msg=" + quote("Komentaro matomumas atnaujintas.")); return
        self.error_page("Veiksmas nerastas.", 404, user, csrf)


def main():
    init_db()
    server = ThreadingHTTPServer((HOST, PORT), App)
    print(f"Questum Training veikia: http://{HOST}:{PORT}")
    print(f"SQLite duomenų bazė: {DB_PATH}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServeris išjungiamas.")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
