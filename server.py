"""Small, dependency-free backend for the Telegram songbook Mini App."""
from __future__ import annotations

import csv
import html
import hashlib
import hmac
import json
import os
import re
import secrets
import sqlite3
import time
from html.parser import HTMLParser
from http.cookies import SimpleCookie
from urllib.parse import urlparse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

ROOT = Path(__file__).resolve().parent
STATE_FILE = Path(os.environ.get("APP_STATE_FILE", str(ROOT / "app_state.json"))).resolve()
BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
OWNER_ID = str(os.environ.get("TELEGRAM_OWNER_ID", ""))
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "")
ADMIN_COOKIE = "pesennik_admin_session"
ADMIN_SESSION_SECONDS = 12 * 60 * 60
SESSIONS: dict[str, float] = {}
LOGIN_FAILURES: dict[str, tuple[int, float]] = {}
HOST, PORT = os.environ.get("APP_HOST", "127.0.0.1"), int(os.environ.get("PORT", "8100"))


def read_csv(path: Path) -> list[dict]:
    with path.open(encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))


def seed_state() -> dict:
    perms = {
        "content.read": "Читать каталог и тексты", "content.edit": "Редактировать каталог и тексты",
        "pages.manage": "Управлять отдельными страницами", "banners.manage": "Управлять рекламой",
    }
    return {
        "permission_definitions": perms,
        "roles": [
            {"id": "owner", "name": "Владелец", "permissions": ["*"]},
            {"id": "admin", "name": "Администратор", "permissions": list(perms)},
            {"id": "editor", "name": "Редактор", "permissions": ["content.read", "content.edit"]},
            {"id": "viewer", "name": "Наблюдатель", "permissions": ["content.read"]},
        ],
        "users": {},
        "work_overrides": {},
        "pages": [{"id": "about", "title": "О сборнике", "content": "«Шри Гаудия-гити-гуччха» — уникальный сборник молитв и песен, наиболее важных для духовной практики гаудия-вайшнавов.\n\nИздание: Москва, «Gaudiya Vedanta Publications» (русское отделение), 2010. 656 страниц. Составлено под руководством Шри Шримад Бхактиведанты Нараяны Госвами Махараджа.\n\n© Swami B.V. Narayan, 2010; © Gaudiya Vedanta Publications, 2010.\n\nЭтот песенник создан на основе указанного издания и может отличаться от печатной книги. Электронный каталог, атрибуции и тексты могли быть отредактированы; тексты, полученные с помощью OCR, являются черновиками и могут содержать ошибки.", "active": True}],
        "banners": {"global": [], "by_page": {}},
    }


def state() -> dict:
    if not STATE_FILE.exists():
        STATE_FILE.write_text(json.dumps(seed_state(), ensure_ascii=False, indent=2), encoding="utf-8")
    return json.loads(STATE_FILE.read_text(encoding="utf-8"))


def save_state(data: dict) -> None:
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(STATE_FILE)


class RichTextSanitizer(HTMLParser):
    """Keep a small formatting allowlist for admin-authored rich text."""
    allowed = {"p", "div", "br", "hr", "strong", "b", "em", "i", "u", "s", "del", "span", "ul", "ol", "li", "blockquote", "h2", "h3", "h4", "a", "img"}
    void = {"br", "hr", "img"}
    blocked = {"script", "style", "iframe", "object", "embed", "svg", "math"}
    safe_classes = {"poem-block", "poem-verse", "poem-prose", "poem-meta", "rich-image"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.output: list[str] = []
        self.stack: list[str] = []
        self.blocked_depth = 0

    def handle_starttag(self, tag, attrs):
        if self.blocked_depth:
            if tag in self.blocked: self.blocked_depth += 1
            return
        if tag in self.blocked:
            self.blocked_depth = 1
            return
        if tag not in self.allowed: return
        safe_attrs = []
        values = dict(attrs)
        if tag == "a":
            href = str(values.get("href", "")).strip()
            parsed = urlparse(href)
            if href and (parsed.scheme.lower() in ("http", "https", "mailto") or (not parsed.scheme and not href.startswith("//"))):
                safe_attrs.append(("href", href))
        if tag == "img":
            src = str(values.get("src", "")).strip()
            parsed = urlparse(src)
            if parsed.scheme.lower() not in ("http", "https") or not parsed.netloc:
                return
            safe_attrs.extend([("src", src), ("alt", str(values.get("alt", ""))[:300])])
        style = str(values.get("style", ""))
        alignment = re.search(r"(?:^|;)\s*text-align\s*:\s*(left|center|right|justify)\s*(?:;|$)", style, re.I)
        if alignment: safe_attrs.append(("style", f"text-align:{alignment.group(1).lower()}"))
        classes = [name for name in str(values.get("class", "")).split() if name in self.safe_classes]
        if classes: safe_attrs.append(("class", " ".join(classes)))
        attr_text = "".join(f' {name}="{html.escape(value, quote=True)}"' for name, value in safe_attrs)
        self.output.append(f"<{tag}{attr_text}>")
        if tag not in self.void: self.stack.append(tag)

    def handle_endtag(self, tag):
        if self.blocked_depth:
            if tag in self.blocked: self.blocked_depth -= 1
            return
        if tag not in self.stack: return
        while self.stack:
            current = self.stack.pop()
            self.output.append(f"</{current}>")
            if current == tag: break

    def handle_data(self, data):
        if not self.blocked_depth: self.output.append(html.escape(data))

    def value(self) -> str:
        while self.stack: self.output.append(f"</{self.stack.pop()}>")
        return "".join(self.output)


def sanitize_rich_text(value) -> str:
    parser = RichTextSanitizer()
    parser.feed(str(value or ""))
    parser.close()
    return parser.value()


def verify_init_data(raw: str) -> dict | None:
    if not BOT_TOKEN or not raw:
        return None
    params = dict(parse_qs(raw, keep_blank_values=True))
    values = {k: v[-1] for k, v in params.items()}
    received = values.pop("hash", "")
    check = "\n".join(f"{k}={values[k]}" for k in sorted(values))
    secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
    expected = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
    try:
        if not hmac.compare_digest(expected, received) or abs(time.time() - int(values.get("auth_date", "0"))) > 86400:
            return None
        return json.loads(values["user"])
    except (ValueError, KeyError, json.JSONDecodeError):
        return None


CATALOG_DB = Path(os.environ.get("PESENNIK_CATALOG_DB", str(ROOT / "catalog.sqlite3"))).resolve()


def load_catalog() -> tuple[list[dict], dict[str, dict], list[dict]]:
    """Load the public catalog from SQLite, seeding it from CSV on first run."""
    CATALOG_DB.parent.mkdir(parents=True, exist_ok=True)
    with sqlite3.connect(CATALOG_DB) as db:
        db.execute("CREATE TABLE IF NOT EXISTS catalog_data (id INTEGER PRIMARY KEY CHECK (id = 1), payload TEXT NOT NULL)")
        row = db.execute("SELECT payload FROM catalog_data WHERE id = 1").fetchone()
        if row:
            payload = json.loads(row[0])
        else:
            catalog_rows = read_csv(ROOT / "catalog_draft.csv")
            payload = {
                "works": [r for r in catalog_rows if r.get("record_type") == "work"],
                "texts": {r["work_id"]: r for r in read_csv(ROOT / "text_stitched_draft.csv")},
                "aliases": [r for r in catalog_rows if r.get("record_type") == "title_alias"],
            }
            db.execute("INSERT INTO catalog_data (id, payload) VALUES (1, ?)", (json.dumps(payload, ensure_ascii=False),))
    return payload["works"], payload["texts"], payload["aliases"]


WORKS, TEXTS, ALIASES = load_catalog()
for work in WORKS:
    tr = TEXTS.get(work["work_id"], {})
    work["text"] = tr.get("text", "")
    work["text_status"] = tr.get("text_status", "Текст не извлечён") or "Текст не извлечён"
    work["text_scope"] = tr.get("text_scope", "")
    work["ocr_confidence"] = tr.get("ocr_confidence", "")
    work["title_aliases"] = [a["title"] for a in ALIASES if a.get("parent_work_id") == work["work_id"]]
    if not work.get("author") or "не установлен" in work.get("author", "").lower():
        work["author"] = "Автор не установлен"


def effective_work(work: dict, overrides: dict | None = None) -> dict:
    overrides = overrides if overrides is not None else state().get("work_overrides", {})
    return {**work, **overrides.get(work["work_id"], {})}


class Handler(BaseHTTPRequestHandler):
    server_version = "Songbook/0.1"

    def log_message(self, fmt, *args):
        print("%s - %s" % (self.address_string(), fmt % args))

    def send_json(self, data, status=200):
        body = json.dumps(data, ensure_ascii=False).encode()
        self.send_response(status); self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body))); self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff"); self.end_headers(); self.wfile.write(body)

    def body(self):
        n = int(self.headers.get("Content-Length", 0))
        if n > 1_000_000: raise ValueError("Запрос слишком большой")
        return json.loads(self.rfile.read(n) or b"{}")

    def identity(self):
        cookies = SimpleCookie(self.headers.get("Cookie", ""))
        session = cookies.get(ADMIN_COOKIE)
        if session:
            expires = SESSIONS.get(session.value, 0)
            if expires > time.time():
                return {"id": "desktop-owner", "first_name": "Владелец (компьютер)", "_desktop": True}, "owner"
            SESSIONS.pop(session.value, None)
        raw = self.headers.get("X-Telegram-Init-Data", "")
        user = verify_init_data(raw)
        if user and str(user.get("id")) == OWNER_ID:
            return user, "owner"
        if not user: return None, None
        role_id = state().get("users", {}).get(str(user.get("id")))
        role = next((r for r in state()["roles"] if r["id"] == role_id), None)
        return (user, role_id) if role else (user, None)

    def allowed(self, permission):
        user, role_id = self.identity()
        if not user or not role_id: return False
        if role_id == "owner" or str(user.get("id")) == OWNER_ID: return True
        data = state(); role = next((r for r in data["roles"] if r["id"] == role_id), {})
        return "*" in role.get("permissions", []) or permission in role.get("permissions", [])

    def is_owner(self):
        user, role = self.identity()
        return bool(user and role == "owner" and (user.get("_desktop") or (OWNER_ID and str(user.get("id")) == OWNER_ID)))

    def do_GET(self):
        u = urlparse(self.path); q = parse_qs(u.query)
        if u.path == "/api/config":
            user, role = self.identity()
            current = state()
            self.send_json({"authenticated": bool(user and role), "role": role, "desktopSession": bool(user and user.get("_desktop")), "appName": "Песенник", "pages": [p for p in current["pages"] if p.get("active")], "banners": current["banners"]}); return
        if u.path == "/api/catalog":
            overrides = state().get("work_overrides", {})
            rows = [effective_work(r, overrides) for r in WORKS]
            search = q.get("q", [""])[0].casefold().strip()
            if search:
                rows = [r for r in rows if search in " ".join([r.get("title", ""), r.get("title_normalized", ""), r.get("author", ""), r.get("text", ""), r.get("aliases", ""), *r.get("title_aliases", [])]).casefold()]
            for field in ("theme", "genre", "language", "author", "subsection"):
                val = q.get(field, [""])[0]
                if val: rows = [r for r in rows if val.casefold() in r.get(field, "").casefold()]
            self.send_json({"items": [{**{k: v for k, v in r.items() if k != "text"}, "has_text": bool(r.get("text"))} for r in rows], "total": len(rows)}); return
        if u.path.startswith("/api/catalog/"):
            wid = u.path.rsplit("/", 1)[-1]
            work = next((r for r in WORKS if r["work_id"] == wid), None)
            if not work: self.send_json({"error": "Произведение не найдено"}, 404); return
            self.send_json(effective_work(work)); return
        if u.path == "/api/admin":
            if not any(self.allowed(p) for p in ("content.read", "content.edit", "pages.manage", "banners.manage")):
                self.send_json({"error": "Доступ запрещён"}, 403); return
            data = state(); user, _ = self.identity()
            owner = self.is_owner()
            response = {"me": user, "role": self.identity()[1], "desktopSession": bool(user and user.get("_desktop")), "roles": data["roles"], "permission_definitions": data["permission_definitions"], "pages": data["pages"], "banners": data["banners"], "ownerConfigured": bool((OWNER_ID and BOT_TOKEN) or ADMIN_PASSWORD)}
            if owner: response["users"] = data["users"]
            self.send_json(response); return
        self.send_error(404)

    def do_POST(self):
        try: data = self.body()
        except Exception as e: self.send_json({"error": str(e)}, 400); return
        if self.path == "/api/login":
            supplied = data.get("password", "")
            if not ADMIN_PASSWORD:
                self.send_json({"error": "Пароль админки не задан. Установите переменную ADMIN_PASSWORD и перезапустите сервер."}, 503); return
            if len(ADMIN_PASSWORD) < 12:
                self.send_json({"error": "Для пароля админки задайте не менее 12 символов"}, 503); return
            client = self.client_address[0]
            failures, locked_until = LOGIN_FAILURES.get(client, (0, 0))
            if locked_until > time.time():
                self.send_json({"error": "Слишком много неудачных попыток. Попробуйте через 15 минут."}, 429); return
            if not isinstance(supplied, str) or len(supplied) > 1024 or not hmac.compare_digest(supplied.encode("utf-8"), ADMIN_PASSWORD.encode("utf-8")):
                failures += 1
                LOGIN_FAILURES[client] = (0, time.time() + 900) if failures >= 5 else (failures, 0)
                self.send_json({"error": "Неверный пароль"}, 401); return
            LOGIN_FAILURES.pop(client, None)
            token = secrets.token_urlsafe(32); SESSIONS[token] = time.time() + ADMIN_SESSION_SECONDS
            secure = "; Secure" if self.headers.get("X-Forwarded-Proto", "").lower() == "https" else ""
            self.send_response(200); self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Set-Cookie", f"{ADMIN_COOKIE}={token}; Path=/; HttpOnly; SameSite=Strict; Max-Age={ADMIN_SESSION_SECONDS}{secure}")
            self.send_header("Cache-Control", "no-store"); self.end_headers(); self.wfile.write(b'{"ok":true}'); return
        if self.path == "/api/logout":
            cookies = SimpleCookie(self.headers.get("Cookie", "")); session = cookies.get(ADMIN_COOKIE)
            if session: SESSIONS.pop(session.value, None)
            self.send_response(200); self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Set-Cookie", f"{ADMIN_COOKIE}=; Path=/; HttpOnly; SameSite=Strict; Max-Age=0")
            self.send_header("Cache-Control", "no-store"); self.end_headers(); self.wfile.write(b'{"ok":true}'); return
        routes = {
            "/api/admin/roles": ("roles.manage", "roles"), "/api/admin/permissions": ("roles.manage", "permission_definitions"),
            "/api/admin/users": ("users.manage", "users"), "/api/admin/pages": ("pages.manage", "pages"),
            "/api/admin/banners": ("banners.manage", "banners"),
        }
        if self.path.startswith("/api/admin/work/") and self.command == "POST":
            if not self.allowed("content.edit"): self.send_json({"error": "Доступ запрещён"}, 403); return
            wid = self.path.rsplit("/", 1)[-1]
            work = next((w for w in WORKS if w["work_id"] == wid), None)
            if not work: self.send_json({"error": "Произведение не найдено"}, 404); return
            current = state(); overrides = current.setdefault("work_overrides", {})
            patch = {k: str(data[k]) for k in ("title", "author", "theme", "genre", "text_status") if k in data}
            if "text" in data: patch["text"] = sanitize_rich_text(data["text"])
            if "title_aliases" in data:
                if not isinstance(data["title_aliases"], list): self.send_json({"error": "Варианты заглавия должны быть списком"}, 400); return
                patch["title_aliases"] = list(dict.fromkeys(str(a).strip() for a in data["title_aliases"] if str(a).strip()))
            overrides[wid] = {**overrides.get(wid, {}), **patch}
            save_state(current)
            self.send_json({"ok": True}); return
        if self.path not in routes: self.send_error(404); return
        permission, key = routes[self.path]
        if key in ("roles", "permission_definitions", "users") and not self.is_owner():
            self.send_json({"error": "Назначать роли и менять разрешения может только владелец"}, 403); return
        if not self.allowed(permission): self.send_json({"error": "Доступ запрещён"}, 403); return
        current = state()
        if key == "roles":
            rows = data.get("items", [])
            if not isinstance(rows, list) or any(not isinstance(x, dict) for x in rows):
                self.send_json({"error": "Ожидался список ролей"}, 400); return
            ids = [x.get("id") for x in rows]
            if len(ids) != len(set(ids)) or any(not isinstance(x.get("id"), str) or not re.fullmatch(r"[a-z0-9_-]{1,40}", x["id"]) or x["id"] == "owner" or not isinstance(x.get("name"), str) or not x["name"].strip() for x in rows):
                self.send_json({"error": "Роль owner зарезервирована; ID должны быть уникальны"}, 400); return
            for r in rows:
                if not isinstance(r.get("permissions"), list) or any(p not in current["permission_definitions"] for p in r.get("permissions", [])):
                    self.send_json({"error": "Неизвестное разрешение"}, 400); return
            current[key] = [{"id": "owner", "name": "Владелец", "permissions": ["*"]}] + rows
            valid_roles = {r["id"] for r in current[key] if r["id"] != "owner"}
            current["users"] = {uid: rid for uid, rid in current["users"].items() if rid in valid_roles}
        elif key == "permission_definitions":
            if not isinstance(data.get("items"), dict) or set(data["items"]) != set(current["permission_definitions"]):
                self.send_json({"error": "Набор доступных действий фиксирован; меняйте ограничения внутри ролей"}, 400); return
            current[key] = data["items"]
        elif key == "users":
            roles = {r["id"] for r in current["roles"] if r["id"] != "owner"}
            if not isinstance(data.get("items"), dict) or any(not str(uid).isdigit() for uid in data["items"]):
                self.send_json({"error": "Укажите числовой Telegram ID для каждого пользователя"}, 400); return
            current[key] = {str(uid): rid for uid, rid in data.get("items", {}).items() if rid in roles and str(uid) != OWNER_ID}
        elif key == "pages":
            if not isinstance(data.get("items"), list): self.send_json({"error": "Ожидался список страниц"}, 400); return
            ids = [x.get("id") for x in data["items"] if isinstance(x, dict)]
            if len(ids) != len(data["items"]) or len(ids) != len(set(ids)) or any(not isinstance(x, str) or x == "catalog" or not re.fullmatch(r"[a-zA-Z0-9_-]{1,60}", x) for x in ids):
                self.send_json({"error": "У страниц должны быть уникальные ID из латинских букв, цифр, _ и -"}, 400); return
            if any(not isinstance(x.get("title"), str) or not x["title"].strip() for x in data["items"]):
                self.send_json({"error": "У каждой страницы должно быть название"}, 400); return
            current[key] = [{**item, "content": sanitize_rich_text(item.get("content", ""))} for item in data["items"]]
            valid_page_ids = {x["id"] for x in data["items"]} | {"catalog"}
            current["banners"]["by_page"] = {pid: items for pid, items in current["banners"].get("by_page", {}).items() if pid in valid_page_ids}
        elif key == "banners":
            if not isinstance(data.get("items"), dict): self.send_json({"error": "Неверный формат баннеров"}, 400); return
            banners = data["items"]
            if not isinstance(banners.get("global", []), list) or not isinstance(banners.get("by_page", {}), dict) or any(not isinstance(group, list) for group in banners.get("by_page", {}).values()):
                self.send_json({"error": "Баннеры должны быть сгруппированы по страницам"}, 400); return
            candidates = list(banners.get("global", [])) + [x for group in banners.get("by_page", {}).values() for x in group]
            for banner in candidates:
                if not isinstance(banner, dict): self.send_json({"error": "Неверная запись баннера"}, 400); return
                for field in ("url", "image"):
                    value = str(banner.get(field, "")).strip()
                    if value and urlparse(value).scheme not in ("https", "http"):
                        self.send_json({"error": "Для ссылок и изображений разрешены только http:// и https://"}, 400); return
            current[key] = {"global": [
                {**banner, "text": sanitize_rich_text(banner.get("text", ""))} for banner in banners.get("global", [])
            ], "by_page": {
                pid: [{**banner, "text": sanitize_rich_text(banner.get("text", ""))} for banner in group]
                for pid, group in banners.get("by_page", {}).items()
            }}
        save_state(current); self.send_json({"ok": True})


class StaticHandler(Handler):
    def do_GET(self):
        if self.path.startswith("/api/"): return super().do_GET()
        path = (ROOT / "web" / (self.path.lstrip("/") or "index.html")).resolve()
        web_root = (ROOT / "web").resolve()
        if not str(path).startswith(str(web_root) + os.sep) and path != web_root / "index.html": self.send_error(403); return
        if path.is_dir(): path = path / "index.html"
        if not path.is_file(): self.send_error(404); return
        raw = path.read_bytes(); self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8" if path.suffix == ".html" else "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(raw))); self.send_header("Cache-Control", "no-cache"); self.end_headers(); self.wfile.write(raw)


if __name__ == "__main__":
    print(f"Песенник: http://{HOST}:{PORT}")
    if not ADMIN_PASSWORD: print("Вход в админку с компьютера отключён: задайте ADMIN_PASSWORD")
    if not BOT_TOKEN or not OWNER_ID: print("Вход администратора через Telegram отключён: задайте TELEGRAM_BOT_TOKEN и TELEGRAM_OWNER_ID")
    ThreadingHTTPServer((HOST, PORT), StaticHandler).serve_forever()
