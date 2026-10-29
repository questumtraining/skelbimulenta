#!/usr/bin/env python3
"""Questum Training bulletin board. Flask + SQLite version for Vercel deployment."""
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
from pathlib import Path
from urllib.parse import quote

from cryptography.fernet import Fernet, InvalidToken
from flask import Flask, request, session, redirect, url_for, make_response

ROOT = Path(__file__).resolve().parent

# Vercel serverless aplinkoje naudojame /tmp katalogą rašymui į DB
if os.environ.get("VERCEL") or os.environ.get("AWS_LAMBDA_FUNCTION_NAME"):
    DB_PATH = Path(os.environ.get("QUESTUM_DB_PATH", "/tmp/questum.sqlite3"))
else:
    DB_PATH = Path(os.environ.get("QUESTUM_DB_PATH", ROOT / "data" / "questum.sqlite3"))

SESSION_HOURS = 12
PBKDF2_ROUNDS = 310_000

app = Flask(__name__, static_folder="static", static_url_path="/static")
app.secret_key = os.environ.get("SECRET_KEY", secrets.token_hex(32))


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
        """)
        user_columns = {row["name"] for row in c.execute("PRAGMA table_info(users)")}
        if "invite_secret" not in user_columns:
            c.execute("ALTER TABLE users ADD COLUMN invite_secret TEXT")
        if "invite_status" not in user_columns:
            c.execute("ALTER TABLE users ADD COLUMN invite_status TEXT NOT NULL DEFAULT ''")
        if "invite_updated_at" not in user_columns:
            c.execute("ALTER TABLE users ADD COLUMN invite_updated_at TEXT")


try:
    init_db()
except Exception as e:
    print(f"DB Init notice: {e}")


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
    public_url = request.host_url.rstrip("/")
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


def markdown(text: str) -> str:
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


def get_current_user():
    user_id = session.get("user_id")
    if not user_id:
        return None
    with db() as c:
        return c.execute("SELECT * FROM users WHERE id=? AND active=1", (user_id,)).fetchone()


def get_csrf():
    if "csrf" not in session:
        session["csrf"] = secrets.token_urlsafe(24)
    return session["csrf"]


def verify_csrf():
    token = request.form.get("csrf", "")
    if not token or token != session.get("csrf"):
        raise ValueError("Saugumo patikra nepavyko. Atnaujinkite puslapį.")


def has_admin():
    with db() as c:
        return c.execute("SELECT 1 FROM users WHERE role='admin' AND active=1 LIMIT 1").fetchone() is not None


def page(title: str, content: str, user=None, active: str = "") -> str:
    msg = request.args.get("msg", "")
    flash = f'<div class="flash">{esc(msg)}</div>' if msg else ""
    csrf = get_csrf()
    if user:
        nav = f'''<header class="topbar"><div class="top-inner"><a class="brand" href="/">Questum <span>TRAINING</span></a><div class="top-actions"><span class="user-name">{esc(user['name'])}</span><form method="post" action="/logout">{csrf_field(csrf)}<button class="link-button" type="submit">Atsijungti</button></form></div></div></header>
        <nav class="main-nav"><div class="nav-inner"><a class="{'current' if active == 'board' else ''}" href="/">Skelbimų lenta</a><a class="{'current' if active == 'mentors' else ''}" href="/mentors">Mentoriai</a>{'<a class="' + ('current' if active == 'admin' else '') + '" href="/admin">Administravimas</a>' if user['role'] == 'admin' else ''}</div></nav>'''
    else:
        nav = '<header class="topbar"><div class="top-inner"><a class="brand" href="/">Questum <span>TRAINING</span></a></div></header>'
    return f'''<!doctype html><html lang="lt"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{esc(title)} · Questum Training</title><link rel="stylesheet" href="/static/style.css"><script src="/static/app.js" defer></script></head><body>{nav}<main class="page-wrap">{flash}{content}</main><footer class="footer">Questum Training · Skelbimų lenta</footer></body></html>'''


@app.route("/")
def home():
    user = get_current_user()
    if not user:
        return redirect(url_for("login", msg="Prisijunkite, kad galėtumėte tęsti."))
    csrf = get_csrf()
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
        # Dalyviams grupių pavadinimų nerodome (visada rodoma bendrinė žymė)
        scope = "Visiems" if row["visibility"] == "all" else (esc(row["group_name"]) if user["role"] == "admin" else "Mokymai")
        attachment = f'<a class="attachment" href="{esc(row["attachment_url"])}" target="_blank" rel="noopener noreferrer">Atidaryti priedą arba nuorodą ↗</a>' if row["attachment_url"] and safe_url(row["attachment_url"]) else ""
        posts.append(f'''<article class="post panel"><div class="post-meta"><span class="badge">{scope}</span><time>{esc(stamp(row['created_at']))}</time></div><h2>{esc(row['title'])}</h2><div class="prose">{markdown(row['body'])}</div>{attachment}<div class="post-author">Atsakingas: {esc(row['author'] or 'Questum Training')}</div></article>''')
    empty = '<div class="panel empty"><h2>Skelbimų dar nėra</h2><p>Naujausi pranešimai pasirodys čia.</p></div>' if not posts else ""
    content = f'''<section class="hero-row"><div><p class="eyebrow">Questum Training</p><h1>Skelbimų lenta</h1><p class="subtitle">Naujausia informacija ir svarbūs pranešimai jūsų mokymams.</p></div>{'<a class="button primary" href="/admin?section=announcements">+ Naujas skelbimas</a>' if user['role']=='admin' else ''}</section>{cards}<section class="content-section"><div class="section-heading"><h2>Naujausi skelbimai</h2><span class="muted">{len(posts)} pranešimai</span></div>{''.join(posts)}{empty}</section>'''
    return page("Skelbimų lenta", content, user, "board")


@app.route("/setup", methods=["GET", "POST"])
def setup():
    if has_admin():
        return redirect(url_for("login"))
    if request.method == "POST":
        name = request.form.get("name", "").strip()
        email = request.form.get("email", "").strip().lower()
        password = request.form.get("password", "")
        confirm = request.form.get("confirm", "")
        if not name or "@" not in email or len(password) < 12 or password != confirm:
            return redirect(url_for("setup", msg="Patikrinkite vardą, el. paštą ir slaptažodį (mažiausiai 12 simbolių)."))
        try:
            with db() as c:
                cur = c.execute("INSERT INTO users(name,email,role,password_hash,active,created_at,updated_at) VALUES(?,?,'admin',?,1,?,?)", (name, email, hash_password(password), now(), now()))
                admin_id = cur.lastrowid
                c.execute("INSERT OR IGNORE INTO groups(name,created_at) VALUES('DaVinci',?)", (now(),))
                c.execute("INSERT INTO announcements(title,body,author_id,visibility,published,created_at,updated_at) VALUES(?,?,?,'all',1,?,?)", ("Sveiki atvykę į Questum Training", "Čia rasite naujausius mokymų pranešimus. Administratorius gali skelbimų lentos turinį, grupes ir mentorių profilius tvarkyti administravimo skydelyje.", admin_id, now(), now()))
            session["user_id"] = admin_id
            return redirect(url_for("admin"))
        except sqlite3.IntegrityError:
            return redirect(url_for("setup", msg="Toks el. pašto adresas jau naudojamas."))
    content = '''<section class="panel narrow"><p class="eyebrow">Pirmasis paleidimas</p><h1>Sukurti administratoriaus paskyrą</h1><p>Šis vienkartinis žingsnis užrakins pradinę sąranką. Pasirinkite ilgą, unikalų slaptažodį.</p><form method="post" action="/setup" class="stack" autocomplete="off"><label>Vardas ir pavardė<input name="name" required maxlength="120" autocomplete="off"></label><label>El. paštas<input name="email" type="email" required maxlength="254" autocomplete="off"></label><label>Slaptažodis<input name="password" type="password" required minlength="12" autocomplete="off"></label><label>Pakartokite slaptažodį<input name="confirm" type="password" required minlength="12" autocomplete="off"></label><button class="button primary">Sukurti paskyrą</button></form></section>'''
    return page("Sąranka", content)


@app.route("/login", methods=["GET", "POST"])
def login():
    if not has_admin():
        return redirect(url_for("setup"))
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()
        password = request.form.get("password", "")
        with db() as c:
            row = c.execute("SELECT * FROM users WHERE email=? AND active=1 AND role IN ('admin','participant')", (email,)).fetchone()
        if not row or not check_password(password, row["password_hash"]):
            return redirect(url_for("login", msg="El. paštas arba slaptažodis neteisingas, arba paskyra neaktyvi."))
        session["user_id"] = row["id"]
        return redirect(url_for("home"))
    content = '''<section class="panel narrow"><p class="eyebrow">Questum Training</p><h1>Prisijungti</h1><p>Prieiga suteikiama tik administratoriaus patvirtintoms paskyroms.</p><form method="post" action="/login" class="stack"><label>El. paštas<input name="email" type="email" required autocomplete="username"></label><label>Slaptažodis<input name="password" type="password" required autocomplete="current-password"></label><button class="button primary">Prisijungti</button></form></section>'''
    return page("Prisijungti", content)


@app.route("/logout", methods=["POST"])
def logout():
    session.clear()
    return redirect(url_for("login"))


@app.route("/mentors")
def mentors():
    user = get_current_user()
    if not user:
        return redirect(url_for("login"))
    csrf = get_csrf()
    query = request.args.get("q", "").strip()
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
    return page("Mentoriai", content, user, "mentors")


@app.route("/mentor")
def mentor_detail():
    user = get_current_user()
    if not user:
        return redirect(url_for("login"))
    csrf = get_csrf()
    mid = request.args.get("id", "")
    with db() as c:
        mentor = c.execute("SELECT m.*,(SELECT updated_at FROM mentor_photos WHERE mentor_id=m.id) AS photo_v,COALESCE(AVG(r.stars),0) AS avg,COUNT(r.id) AS count FROM mentors m LEFT JOIN ratings r ON r.mentor_id=m.id WHERE m.id=? AND (m.active=1 OR ?='admin') GROUP BY m.id", (mid, user["role"])).fetchone()
        if not mentor:
            return page("Pranešimas", '<section class="panel narrow"><h1>Pranešimas</h1><p>Mentorius nerastas.</p><p><a class="button" href="/mentors">Grįžti atgal</a></p></section>', user)
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
    return page(mentor["name"], content, user, "mentors")


@app.route("/mentor/photo")
def mentor_photo():
    user = get_current_user()
    if not user:
        return redirect(url_for("login"))
    mid = request.args.get("id", "")
    with db() as c:
        row = c.execute("SELECT p.content_type,p.data FROM mentor_photos p JOIN mentors m ON m.id=p.mentor_id WHERE p.mentor_id=? AND (m.active=1 OR ?='admin')", (mid if mid.isdigit() else 0, user["role"])).fetchone()
    if not row:
        return "Nuotrauka nerasta", 404
    res = make_response(bytes(row["data"]))
    res.headers["Content-Type"] = row["content_type"]
    res.headers["Cache-Control"] = "private, max-age=86400"
    return res


@app.route("/rating/save", methods=["POST"])
def rating_save():
    user = get_current_user()
    if not user or user["role"] != "participant":
        return redirect(url_for("login"))
    try:
        verify_csrf()
        mid = int(request.form.get("mentor_id", 0))
        stars = int(request.form.get("stars", 0))
        comment = request.form.get("comment", "").strip()
        if stars < 1 or stars > 5 or len(comment) > 2000:
            raise ValueError("Pasirinkite 1–5 žvaigždutes; komentaras gali būti iki 2 000 simbolių.")
        with db() as c:
            mentor = c.execute("SELECT active FROM mentors WHERE id=?", (mid,)).fetchone()
            if not mentor or not mentor["active"]:
                raise ValueError("Šio mentoriaus įvertinti negalima.")
            prior = c.execute("SELECT id FROM ratings WHERE mentor_id=? AND user_id=?", (mid, user["id"])).fetchone()
            timestamp = now()
            if prior:
                c.execute("UPDATE ratings SET stars=?,comment=?,updated_at=? WHERE id=?", (stars, comment, timestamp, prior["id"]))
            else:
                c.execute("INSERT INTO ratings(mentor_id,user_id,stars,comment,created_at,updated_at) VALUES(?,?,?,?,?,?)", (mid, user["id"], stars, comment, timestamp, timestamp))
        return redirect(f"/mentor?id={mid}&msg=" + quote("Vertinimas išsaugotas."))
    except Exception as exc:
        return redirect(f"/mentor?id={request.form.get('mentor_id', '')}&msg=" + quote(str(exc)[:220]))


@app.route("/rating/delete", methods=["POST"])
def rating_delete():
    user = get_current_user()
    if not user:
        return redirect(url_for("login"))
    try:
        verify_csrf()
        mid = int(request.form.get("mentor_id", 0))
        with db() as c:
            c.execute("DELETE FROM ratings WHERE mentor_id=? AND user_id=?", (mid, user["id"]))
        return redirect(f"/mentor?id={mid}&msg=" + quote("Vertinimas pašalintas."))
    except Exception as exc:
        return redirect(f"/mentor?id={request.form.get('mentor_id', '')}&msg=" + quote(str(exc)[:220]))


@app.route("/admin")
def admin():
    user = get_current_user()
    if not user or user["role"] != "admin":
        return redirect(url_for("login", msg="Šiai sričiai reikia administratoriaus teisių."))
    csrf = get_csrf()
    section = request.args.get("section", "users")
    if section not in ("users", "announcements", "mentors", "reviews"):
        section = "users"
    sections = [("users", "Vartotojai"), ("mentors", "Mentoriai"), ("announcements", "Skelbimai"), ("reviews", "Vertinimai")]
    tabs = ''.join(f'<a class="tab{" active" if section == key else ""}" href="/admin?section={key}">{label}</a>' for key, label in sections)
    
    with db() as c:
        counts = {key: c.execute(sql).fetchone()[0] for key, sql in {
            "users": "SELECT COUNT(*) FROM users WHERE active=1",
            "mentors": "SELECT COUNT(*) FROM mentors WHERE active=1",
            "announcements": "SELECT COUNT(*) FROM announcements",
            "reviews": "SELECT COUNT(*) FROM ratings"}.items()}
        groups = c.execute("SELECT * FROM groups ORDER BY name").fetchall()
        
        body = ""
        if section == "users":
            rows = c.execute("SELECT u.*,GROUP_CONCAT(ug.group_id) AS group_ids FROM users u LEFT JOIN user_groups ug ON ug.user_id=u.id GROUP BY u.id ORDER BY u.name").fetchall()
            group_cards = [f'''<div class="group-row"><form method="post" action="/admin/group/save" class="inline-fields">{csrf_field(csrf)}<input type="hidden" name="group_id" value="{g["id"]}"><label>Grupė<input name="name" value="{esc(g["name"])}" maxlength="100" required></label><button class="button secondary small">Išsaugoti</button></form><form method="post" action="/admin/group/delete" data-confirm="Pašalinti grupę?">{csrf_field(csrf)}<input type="hidden" name="group_id" value="{g["id"]}"><button class="link-button danger">Pašalinti</button></form></div>''' for g in groups]
            cards = []
            for row in rows:
                g_ids = set((row["group_ids"] or "").split(","))
                group_options = "".join(f'<option value="{g["id"]}"{" selected" if str(g["id"]) in g_ids else ""}>{esc(g["name"])}</option>' for g in groups)
                role_options = "".join(f'<option value="{r}"{" selected" if row["role"] == r else ""}>{lbl}</option>' for r, lbl in (("participant", "Dalyvis"), ("admin", "Administratorius")))
                cards.append(f'''<article class="manage-card"><form method="post" action="/admin/user/save" class="stack">{csrf_field(csrf)}<input type="hidden" name="user_id" value="{row["id"]}"><div class="form-grid"><label>Vardas<input name="name" value="{esc(row["name"])}" maxlength="120" required></label><label>El. paštas<input name="email" type="email" value="{esc(row["email"])}" maxlength="254" required></label><label>Rolė<select name="role">{role_options}</select></label><label>Grupės<select name="group_ids" multiple size="2">{group_options}</select></label></div><div class="row-end"><label class="check"><input type="checkbox" name="active" value="1"{" checked" if row["active"] else ""}> Aktyvi paskyra</label><button class="button secondary small">Išsaugoti</button></div></form>{invitation_html(row,csrf,"users")}<form method="post" action="/admin/user/delete" class="delete-form" data-confirm="Pašalinti vartotoją?">{csrf_field(csrf)}<input type="hidden" name="user_id" value="{row["id"]}"><button class="link-button danger">Pašalinti vartotoją</button></form></article>''')
            group_options = "".join(f'<option value="{g["id"]}">{esc(g["name"])}</option>' for g in groups)
            body = f'''<section class="admin-section"><div class="manage-grid">{''.join(cards) or '<p class="muted">Vartotojų nėra.</p>'}</div><section class="panel"><h3>Pridėti vartotoją</h3><form method="post" action="/admin/user/save" class="stack">{csrf_field(csrf)}<div class="form-grid"><label>Vardas<input name="name" maxlength="120" required></label><label>El. paštas<input name="email" type="email" maxlength="254" required></label><label>Rolė<select name="role"><option value="participant">Dalyvis</option><option value="admin">Administratorius</option></select></label><label>Grupė<select name="group_ids"><option value="">— Be grupės —</option>{group_options}</select></label></div><button class="button primary">Sukurti paskyrą</button></form></section><section class="panel"><h3>Importuoti dalyvius (CSV)</h3><form method="post" action="/admin/users/import" enctype="multipart/form-data" class="inline-fields">{csrf_field(csrf)}<label>CSV failas<input type="file" name="csv_file" accept=".csv,text/csv" required></label><button class="button secondary">Importuoti</button></form></section><details class="panel group-settings"><summary>Grupių valdymas</summary><div class="group-list">{''.join(group_cards)}</div><form method="post" action="/admin/group/save" class="inline-fields group-create">{csrf_field(csrf)}<label>Nauja grupė<input name="name" maxlength="100" placeholder="Pvz., DaVinci 2026" required></label><button class="button secondary">Sukurti grupę</button></form></details></section>'''

        elif section == "mentors":
            rows = c.execute("SELECT m.*,(SELECT updated_at FROM mentor_photos WHERE mentor_id=m.id) AS photo_v,COALESCE(AVG(r.stars),0) AS avg,COUNT(r.id) AS count FROM mentors m LEFT JOIN ratings r ON r.mentor_id=m.id GROUP BY m.id ORDER BY m.name").fetchall()
            cards = [f'''<article class="manage-card">{mentor_form(csrf, r)}<form method="post" action="/admin/mentor/delete" class="delete-form" data-confirm="Pašalinti mentoriaus profilį?">{csrf_field(csrf)}<input type="hidden" name="mentor_id" value="{r["id"]}"><button class="link-button danger">Pašalinti mentorių</button></form></article>''' for r in rows]
            body = f'''<section class="admin-section"><div class="manage-grid">{''.join(cards) or '<p class="muted">Mentorių profilių nėra.</p>'}</div><section class="panel"><h3>Pridėti mentorių</h3>{mentor_form(csrf)}</section></section>'''

        elif section == "announcements":
            rows = c.execute("SELECT a.*,g.name AS group_name FROM announcements a LEFT JOIN groups g ON g.id=a.group_id ORDER BY a.created_at DESC").fetchall()
            cards = []
            for r in rows:
                vis = ''.join(f'<option value="{v}"{" selected" if r["visibility"]==v else ""}>{lbl}</option>' for v, lbl in (("all", "Visiems dalyviams"), ("group", "Pasirinktai grupei")))
                g_opts = ''.join(f'<option value="{g["id"]}"{" selected" if str(r["group_id"] or "")==str(g["id"]) else ""}>{esc(g["name"])}</option>' for g in groups)
                cards.append(f'''<article class="manage-card"><form method="post" action="/admin/announcement/save" class="stack">{csrf_field(csrf)}<input type="hidden" name="announcement_id" value="{r['id']}"><div class="form-grid"><label>Pavadinimas<input name="title" value="{esc(r['title'])}" required maxlength="200"></label><label>Matomumas<select name="visibility">{vis}</select></label><label>Grupė<select name="group_id"><option value="">— Pasirinkti grupę —</option>{g_opts}</select></label><label>Nuoroda / priedas<input name="attachment_url" type="url" value="{esc(r['attachment_url'])}" placeholder="https://…"></label></div><label>Tekstas<textarea name="body" rows="6" required>{esc(r['body'])}</textarea></label><div class="row-end"><label class="check"><input type="checkbox" name="published" value="1"{' checked' if r['published'] else ''}> Paskelbtas</label><button class="button secondary">Išsaugoti</button></div></form><form method="post" action="/admin/announcement/delete" class="delete-form" data-confirm="Pašalinti skelbimą?">{csrf_field(csrf)}<input type="hidden" name="announcement_id" value="{r['id']}"><button class="link-button danger">Pašalinti skelbimą</button></form></article>''')
            g_opts = ''.join(f'<option value="{g["id"]}">{esc(g["name"])}</option>' for g in groups)
            body = f'''<section class="admin-section"><div class="manage-grid">{''.join(cards) or '<p class="muted">Skelbimų nėra.</p>'}</div><section class="panel"><h3>Sukurti skelbimą</h3><form method="post" action="/admin/announcement/save" class="stack">{csrf_field(csrf)}<div class="form-grid"><label>Pavadinimas<input name="title" required maxlength="200"></label><label>Matomumas<select name="visibility"><option value="all">Visiems dalyviams</option><option value="group">Pasirinktai grupei</option></select></label><label>Grupė<select name="group_id"><option value="">— Pasirinkti grupę —</option>{g_opts}</select></label><label>Nuoroda / priedas<input name="attachment_url" type="url" placeholder="https://…"></label></div><label>Tekstas<textarea name="body" rows="6" required placeholder="Parašykite tekstą…"></textarea></label><label class="check"><input type="checkbox" name="published" value="1"> Paskelbti iš karto</label><button class="button primary">Sukurti skelbimą</button></form></section></section>'''

        elif section == "reviews":
            rows = c.execute("SELECT r.*,m.name AS mentor_name,u.name AS user_name,u.email AS user_email FROM ratings r JOIN mentors m ON m.id=r.mentor_id JOIN users u ON u.id=r.user_id ORDER BY r.updated_at DESC").fetchall()
            cards = [f'''<article class="manage-card review-admin"><div><h3>{esc(r['mentor_name'])} <span class="stars">{"★"*r['stars']}{"☆"*(5-r['stars'])}</span></h3><p>{esc(r['comment'] or 'Komentaro nėra.')}</p><p class="muted">Pateikė {esc(r['user_name'])} ({esc(r['user_email'])})</p></div><form method="post" action="/admin/review/moderate" class="row-end">{csrf_field(csrf)}<input type="hidden" name="rating_id" value="{r['id']}"><label class="check"><input type="checkbox" name="hidden" value="1"{' checked' if r['comment_hidden'] else ''}> Slėpti komentarą</label><button class="button secondary">Išsaugoti</button></form></article>''' for r in rows]
            body = f'''<section class="admin-section"><div class="manage-grid">{''.join(cards) or '<p class="muted">Vertinimų nėra.</p>'}</div></section>'''

    content = f'''<section class="hero-row"><div><p class="eyebrow">Valdymo aplinka</p><h1>Administravimas</h1></div></section><div class="stat-grid admin-stats">{''.join(f'<div class="stat-card"><strong>{counts[k]}</strong><span>{lbl}</span></div>' for k,lbl in (("users","Vartotojai"),("mentors","Mentoriai"),("announcements","Skelbimai"),("reviews","Vertinimai")))}</div><div class="tabs">{tabs}</div>{body}'''
    return page("Administravimas", content, user, "admin")


@app.route("/admin/user/save", methods=["POST"])
def admin_user_save():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        uid = request.form.get("user_id")
        name = request.form.get("name", "").strip()
        email = request.form.get("email", "").strip().lower()
        role = request.form.get("role", "participant")
        group_ids = request.form.getlist("group_ids")
        if not name or "@" not in email: raise ValueError("Neteisingas vardas arba el. paštas.")
        with db() as c:
            if uid:
                uid = int(uid)
                old = c.execute("SELECT role FROM users WHERE id=?", (uid,)).fetchone()
                active = 1 if request.form.get("active") == "1" else 0
                if uid == user["id"] and (not active or role != "admin"):
                    raise ValueError("Negalite išjungti arba pakeisti savo administratoriaus teisių.")
                if old and old["role"] == "admin" and (not active or role != "admin"):
                    others = c.execute("SELECT COUNT(*) FROM users WHERE role='admin' AND active=1 AND id<>?", (uid,)).fetchone()[0]
                    if not others:
                        raise ValueError("Turi likti bent vienas aktyvus administratorius.")
                c.execute("UPDATE users SET name=?,email=?,role=?,active=?,updated_at=? WHERE id=?", (name, email, role, active, now(), uid))
                c.execute("DELETE FROM user_groups WHERE user_id=?", (uid,))
                account_id = uid
            else:
                pwd = generate_password()
                cur = c.execute("INSERT INTO users(name,email,role,password_hash,active,created_at,updated_at,invite_secret,invite_status,invite_updated_at) VALUES(?,?,?,?,1,?,?,?,?,?)",
                                (name, email, hash_password(pwd), now(), now(), encrypt_invite_password(pwd), "not_configured", now()))
                account_id = cur.lastrowid
            for gid in group_ids:
                if gid: c.execute("INSERT OR IGNORE INTO user_groups(user_id,group_id) VALUES(?,?)", (account_id, int(gid)))
        return redirect(url_for("admin", section="users", msg="Vartotojo duomenys išsaugoti."))
    except Exception as exc:
        return redirect(url_for("admin", section="users", msg=str(exc)[:220]))


@app.route("/admin/user/delete", methods=["POST"])
def admin_user_delete():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        uid = int(request.form.get("user_id", 0))
        if uid == user["id"]: raise ValueError("Negalite ištrinti savo paskyros.")
        with db() as c:
            row = c.execute("SELECT role FROM users WHERE id=?", (uid,)).fetchone()
            if row and row["role"] == "admin":
                others = c.execute("SELECT COUNT(*) FROM users WHERE role='admin' AND active=1 AND id<>?", (uid,)).fetchone()[0]
                if not others:
                    raise ValueError("Turi likti bent vienas aktyvus administratorius.")
            c.execute("DELETE FROM users WHERE id=?", (uid,))
        return redirect(url_for("admin", section="users", msg="Vartotojas pašalintas."))
    except Exception as exc:
        return redirect(url_for("admin", section="users", msg=str(exc)[:220]))


@app.route("/admin/mentor/save", methods=["POST"])
def admin_mentor_save():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        mid = request.form.get("mentor_id")
        photo = request.files.get("photo")
        photo_data = (photo.content_type, photo.read()) if photo and photo.filename else None
        save_mentor({
            "name": request.form.get("name"), "email": request.form.get("email"),
            "phone": request.form.get("phone"), "bio": request.form.get("bio"),
            "specialties": request.form.get("specialties"), "active": request.form.get("active") == "1"
        }, photo_data, request.form.get("remove_photo") == "1", int(mid) if mid and mid.isdigit() else None)
        return redirect(url_for("admin", section="mentors", msg="Mentoriaus profilis išsaugotas."))
    except Exception as exc:
        return redirect(url_for("admin", section="mentors", msg=str(exc)[:220]))


@app.route("/admin/mentor/delete", methods=["POST"])
def admin_mentor_delete():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        mid = int(request.form.get("mentor_id", 0))
        delete_mentor(mid)
        return redirect(url_for("admin", section="mentors", msg="Mentoriaus profilis pašalintas."))
    except Exception as exc:
        return redirect(url_for("admin", section="mentors", msg=str(exc)[:220]))


@app.route("/admin/group/save", methods=["POST"])
def admin_group_save():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        name = request.form.get("name", "").strip()
        gid = request.form.get("group_id")
        if not name: raise ValueError("Įrašykite grupės pavadinimą.")
        with db() as c:
            if gid: c.execute("UPDATE groups SET name=? WHERE id=?", (name, int(gid)))
            else: c.execute("INSERT INTO groups(name,created_at) VALUES(?,?)", (name, now()))
        return redirect(url_for("admin", section="users", msg="Grupė išsaugota."))
    except Exception as exc:
        return redirect(url_for("admin", section="users", msg=str(exc)[:220]))


@app.route("/admin/group/delete", methods=["POST"])
def admin_group_delete():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        gid = int(request.form.get("group_id", 0))
        with db() as c: c.execute("DELETE FROM groups WHERE id=?", (gid,))
        return redirect(url_for("admin", section="users", msg="Grupė pašalinta."))
    except Exception as exc:
        return redirect(url_for("admin", section="users", msg=str(exc)[:220]))


@app.route("/admin/announcement/save", methods=["POST"])
def admin_announcement_save():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        aid = request.form.get("announcement_id")
        title = request.form.get("title", "").strip()
        body = request.form.get("body", "").strip()
        visibility = request.form.get("visibility", "all")
        gid = request.form.get("group_id") or None
        attachment = request.form.get("attachment_url", "").strip()
        if not title or not body: raise ValueError("Įrašykite pavadinimą ir tekstą.")
        published = 1 if request.form.get("published") == "1" else 0
        timestamp = now()
        with db() as c:
            if aid:
                c.execute("UPDATE announcements SET title=?,body=?,visibility=?,group_id=?,attachment_url=?,published=?,updated_at=? WHERE id=?",
                          (title, body, visibility, gid if visibility == "group" else None, attachment, published, timestamp, int(aid)))
            else:
                c.execute("INSERT INTO announcements(title,body,author_id,visibility,group_id,attachment_url,published,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?)",
                          (title, body, user["id"], visibility, gid if visibility == "group" else None, attachment, published, timestamp, timestamp))
        return redirect(url_for("admin", section="announcements", msg="Skelbimas išsaugotas."))
    except Exception as exc:
        return redirect(url_for("admin", section="announcements", msg=str(exc)[:220]))


@app.route("/admin/announcement/delete", methods=["POST"])
def admin_announcement_delete():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        aid = int(request.form.get("announcement_id", 0))
        with db() as c: c.execute("DELETE FROM announcements WHERE id=?", (aid,))
        return redirect(url_for("admin", section="announcements", msg="Skelbimas pašalintas."))
    except Exception as exc:
        return redirect(url_for("admin", section="announcements", msg=str(exc)[:220]))


@app.route("/admin/review/moderate", methods=["POST"])
def admin_review_moderate():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        rid = int(request.form.get("rating_id", 0))
        hidden = 1 if request.form.get("hidden") == "1" else 0
        with db() as c: c.execute("UPDATE ratings SET comment_hidden=?,updated_at=? WHERE id=?", (hidden, now(), rid))
        return redirect(url_for("admin", section="reviews", msg="Vertinimo matomumas atnaujintas."))
    except Exception as exc:
        return redirect(url_for("admin", section="reviews", msg=str(exc)[:220]))


@app.route("/admin/users/import", methods=["POST"])
def admin_users_import():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        file = request.files.get("csv_file")
        if not file or not file.filename.endswith(".csv"): raise ValueError("Pasirinkite galiojantį CSV failą.")
        raw = file.read().decode("utf-8-sig")
        reader = csv.DictReader(io.StringIO(raw))
        headers = {col.lower(): col for col in (reader.fieldnames or [])}
        if "email" not in headers: raise ValueError("CSV faile turi būti stulpelis 'email'.")
        added = 0
        with db() as c:
            for row in reader:
                email = (row.get(headers["email"]) or "").strip().lower()
                if not email or "@" not in email: continue
                name = (row.get(headers.get("name", "name")) or email.split("@")[0]).strip()
                if c.execute("SELECT 1 FROM users WHERE email=?", (email,)).fetchone(): continue
                pwd = generate_password()
                c.execute("INSERT INTO users(name,email,role,password_hash,active,created_at,updated_at,invite_secret,invite_status,invite_updated_at) VALUES(?,?,'participant',?,1,?,?,?,?,?)",
                          (name, email, hash_password(pwd), now(), now(), encrypt_invite_password(pwd), "not_configured", now()))
                added += 1
        return redirect(url_for("admin", section="users", msg=f"Sėkmingai importuota {added} vartotojų."))
    except Exception as exc:
        return redirect(url_for("admin", section="users", msg=str(exc)[:220]))


@app.route("/admin/account/regenerate", methods=["POST"])
def admin_account_regenerate():
    user = get_current_user()
    if not user or user["role"] != "admin": return redirect(url_for("login"))
    try:
        verify_csrf()
        uid = int(request.form.get("user_id", 0))
        pwd = generate_password()
        with db() as c:
            c.execute("UPDATE users SET password_hash=?,invite_secret=?,invite_status='not_configured',invite_updated_at=?,updated_at=? WHERE id=?",
                      (hash_password(pwd), encrypt_invite_password(pwd), now(), now(), uid))
        return redirect(url_for("admin", section="users", msg="Naujas slaptažodis sugeneruotas."))
    except Exception as exc:
        return redirect(url_for("admin", section="users", msg=str(exc)[:220]))


if __name__ == "__main__":
    init_db()
    app.run(host="127.0.0.1", port=8000, debug=True)
