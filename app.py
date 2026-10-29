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

# Vercel serverless aplinkoje naudoti /tmp katalogą, kad veiktų rašymas į DB
if os.environ.get("VERCEL") or os.environ.get("AWS_LAMBDA_FUNCTION_NAME"):
    DB_PATH = Path(os.environ.get("QUESTUM_DB_PATH", "/tmp/questum.sqlite3"))
else:
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

        mentor_columns = {row["name"] for row in c.execute("PRAGMA table_info(mentors)")}
        if "user_id" in mentor_columns:
            for account in c.execute("SELECT u.id,u.name,u.email,u.active FROM users u LEFT JOIN mentors m ON m.user_id=u.id WHERE u.role='mentor' AND m.id IS NULL").fetchall():
                c.execute("INSERT INTO mentors(user_id,name,email,active,created_at,updated_at) VALUES(?,?,?,?,?,?)", (account["id"],account["name"],account["email"],account["active"],now(),now()))
            c.execute("UPDATE mentors SET user_id=NULL WHERE user_id IS NOT NULL")
        c.execute("DELETE FROM users WHERE role='mentor'")
        c.execute("UPDATE announcements SET visibility='all',group_id=NULL,published=0 WHERE visibility='mentors'")


# Užtikriname, kad DB lentelės bus sukurtos užkraunant modulį
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
                key_file.write(Fernet.generate
