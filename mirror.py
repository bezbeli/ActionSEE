#!/usr/bin/env python3
"""Mirror the ActionSEE WordPress sites to static files.

Pretty permalinks such as /news/ are saved as news/index.html. Links keep that
path: only the site hostname is rewritten to a root-relative URL, so the
address bar never gains index.html or a .html suffix.
"""

from __future__ import annotations

import gzip
import html as html_lib
import re
import sys
import threading
import time
import urllib.error
import urllib.request
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, unquote, urljoin, urlparse
from xml.etree import ElementTree

UA = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)
ROOT = Path(__file__).resolve().parent
GITHUB_FILE_LIMIT = 100 * 1024 * 1024
ASSET_WORKERS = 6

ASSET_EXTENSIONS = {
    ".css", ".js", ".mjs", ".map",
    ".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".ico", ".avif", ".bmp",
    ".woff", ".woff2", ".ttf", ".eot", ".otf",
    ".pdf", ".mp4", ".webm", ".mp3", ".ogg",
    ".ppt", ".pptx", ".doc", ".docx", ".xls", ".xlsx", ".zip", ".csv",
    ".xml", ".txt", ".json", ".html", ".htm",
}
TEXT_EXTENSIONS = {".css", ".js", ".mjs", ".svg", ".map", ".json", ".xml", ".txt", ".html", ".htm"}
SKIP_FILENAMES = {
    "xmlrpc.php",
    "wp-login.php",
    "wp-cron.php",
    "wp-comments-post.php",
    "wp-signup.php",
    "wp-activate.php",
    "wp-trackback.php",
    "wp-mail.php",
}
SKIP_REST_TYPES = {
    "attachment",
    "nav_menu_item",
    "wp_block",
    "wp_template",
    "wp_template_part",
    "wp_global_styles",
    "wp_navigation",
    "wp_font_family",
    "wp_font_face",
}

# Don't match JavaScript such as URL.createObjectURL(...).
CSS_URL_RE = re.compile(r"(?<![A-Za-z0-9_-])url\(\s*(['\"]?)(.*?)\1\s*\)", re.I | re.S)
CSS_IMPORT_RE = re.compile(r"@import\s+(?:url\(\s*)?(['\"])(.*?)\1", re.I)

SITES = (
    ("https://actionsee.org", "actionsee.org"),
    ("https://resource.actionsee.org", "resource.actionsee.org"),
)


def fetch(url: str, retries: int = 4, timeout: int = 60) -> dict:
    headers = {
        "User-Agent": UA,
        "Accept": "*/*",
        "Accept-Language": "en",
    }
    last_error = "unknown error"
    for attempt in range(retries):
        try:
            request = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(request, timeout=timeout) as response:
                data = response.read()
                encoding = (response.headers.get("Content-Encoding") or "").lower()
                if encoding == "gzip" or data[:2] == b"\x1f\x8b":
                    try:
                        data = gzip.decompress(data)
                    except gzip.BadGzipFile:
                        pass
                return {
                    "status": response.status,
                    "url": response.geturl(),
                    "ctype": response.headers.get("Content-Type") or "",
                    "headers": response.headers,
                    "data": data,
                    "error": "",
                }
        except urllib.error.HTTPError as error:
            body = error.read() if error.fp else b""
            if error.code in {429, 500, 502, 503, 504} and attempt + 1 < retries:
                time.sleep(1.5 * (attempt + 1))
                last_error = f"HTTP {error.code}"
                continue
            return {
                "status": error.code,
                "url": url,
                "ctype": error.headers.get("Content-Type") if error.headers else "",
                "headers": error.headers,
                "data": body,
                "error": f"HTTP {error.code}",
            }
        except Exception as error:  # noqa: BLE001 - retry any transport failure
            last_error = str(error)
            time.sleep(1.5 * (attempt + 1))
    return {
        "status": 0,
        "url": url,
        "ctype": "",
        "headers": {},
        "data": b"",
        "error": last_error,
    }


class LinkParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.found: list[str] = []
        self._in_style = False

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._take(tag, attrs)
        if tag.lower() == "style":
            self._in_style = True

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() == "style":
            self._in_style = False

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._take(tag, attrs)

    def handle_data(self, data: str) -> None:
        if self._in_style:
            self.found.extend(css_references(data))

    def _take(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        names = {
            "href",
            "src",
            "poster",
            "data-src",
            "data-lazy-src",
            "data-original",
            "data-bg",
            "data-background",
        }
        if tag.lower() in {"object", "embed"}:
            names.add("data")
        for key, value in attrs:
            if not value:
                continue
            name = key.lower()
            if name in {"srcset", "data-srcset", "imagesrcset"}:
                self.found.extend(split_srcset(value))
            elif name in names:
                self.found.append(value)
            elif name == "style":
                self.found.extend(css_references(value))


def split_srcset(value: str) -> list[str]:
    urls = []
    for part in value.split(","):
        piece = part.strip()
        if not piece:
            continue
        urls.append(piece.split()[0])
    return urls


def css_references(text: str) -> list[str]:
    found = []
    for match in CSS_URL_RE.finditer(text):
        value = match.group(2).strip()
        if value and not value.startswith("data:"):
            found.append(value)
    for match in CSS_IMPORT_RE.finditer(text):
        value = match.group(2).strip()
        if value and not value.startswith("data:"):
            found.append(value)
    return found


class Mirror:
    def __init__(self, origin: str, folder: str) -> None:
        self.origin = origin.rstrip("/")
        self.host = urlparse(self.origin).netloc
        self.dest = ROOT / folder
        self.pages = 0
        self.assets_saved = 0
        self.errors: list[str] = []
        self.large: list[str] = []
        self.asset_jobs: dict[str, str] = {}
        self.queued_assets: set[str] = set()
        self.lock = threading.Lock()
        self.host_url_re = re.compile(
            rf"https?://{re.escape(self.host)}(/[^\s\"'<>)&]*)",
            re.I,
        )
        self.root_asset_re = re.compile(
            r"(?<![A-Za-z0-9_])(/(?:app|wp-content|wp)/[^\s\"'<>)&]*)"
        )

    def run(self) -> None:
        self.dest.mkdir(parents=True, exist_ok=True)
        (self.dest / ".nojekyll").write_text("")
        print(f"\n== {self.origin} -> {self.dest}", flush=True)
        seeds = [self.origin + "/"]
        seeds.extend(self.sitemap_urls())
        seeds.extend(self.rest_links())
        print(f"  seeds {len(seeds)}", flush=True)
        self.crawl(seeds)
        media = self.media_urls()
        print(f"  media files {len(media)}", flush=True)
        for url in media:
            self.consider(url, self.origin + "/")
        self.download_assets()
        self.summary()

    def note_error(self, message: str) -> None:
        with self.lock:
            self.errors.append(message)

    def url_for(self, path: str) -> str:
        encoded = "/".join(quote(segment, safe="") for segment in path.split("/"))
        return self.origin + encoded

    def extension(self, path: str) -> str:
        name = path.rstrip("/").split("/")[-1]
        if "." not in name:
            return ""
        return "." + name.rsplit(".", 1)[-1].lower()

    def is_asset(self, path: str) -> bool:
        return self.extension(path) in ASSET_EXTENSIONS

    def should_skip(self, path: str) -> bool:
        low = path.lower()
        if low.startswith("/cdn-cgi"):
            return True
        if low.startswith("/wp-json") or "/wp-json/" in low or low.startswith("/wp/wp-json"):
            return True
        if "/wp-admin" in low:
            return True
        if low in {"/feed", "/feed/"} or low.endswith("/feed") or low.endswith("/feed/") or "/feed/" in low:
            return True
        name = low.rstrip("/").split("/")[-1]
        if name in SKIP_FILENAMES or name.endswith(".php"):
            return True
        if "<" in path or ">" in path or "\n" in path or "\x00" in path:
            return True
        return False

    def looks_like_url(self, raw: str) -> bool:
        if raw.startswith(("#", "mailto:", "tel:", "javascript:", "data:")):
            return False
        if raw.startswith(("/", "http://", "https://", "//", "./", "../")):
            return True
        return "/" in raw or "." in raw

    def normalize_path(self, path: str, trailing: bool) -> str | None:
        path = path.split("&", 1)[0].split("?", 1)[0].split("#", 1)[0]
        path = unquote(path)
        if not path.startswith("/"):
            path = "/" + path
        parts: list[str] = []
        for part in path.split("/"):
            if part in {"", "."}:
                continue
            if part == "..":
                return None
            parts.append(part)
        if any(len(part.encode("utf-8")) > 255 for part in parts):
            return None
        built = "/" + "/".join(parts)
        if built == "/":
            return "/"
        if trailing:
            return built + "/"
        return built

    def classify(self, raw: str, base: str) -> tuple[str, str, str] | None:
        raw = html_lib.unescape(raw.strip().strip("\"'"))
        raw = raw.rstrip(".,;")
        if not raw or not self.looks_like_url(raw):
            return None
        absolute = urljoin(base, raw)
        parsed = urlparse(absolute)
        if parsed.scheme not in {"http", "https"} or parsed.netloc.lower() != self.host.lower():
            return None
        trailing = (parsed.path or "/").endswith("/")
        path = self.normalize_path(parsed.path or "/", trailing)
        if not path or self.should_skip(path):
            return None
        if self.is_asset(path):
            if path.endswith("/"):
                path = path.rstrip("/")
            return ("asset", self.url_for(path), path)
        if path != "/" and not path.endswith("/"):
            path += "/"
        return ("page", self.url_for(path), path)

    def rewrite(self, text: str) -> str:
        host = self.host
        for prefix in (
            f"https://{host}",
            f"http://{host}",
            f"https:\\/\\/{host}",
            f"http:\\/\\/{host}",
            f"//{host}",
            f"https%3A%2F%2F{host}",
            f"http%3A%2F%2F{host}",
            f"https%3a%2f%2f{host}",
            f"http%3a%2f%2f{host}",
        ):
            text = text.replace(prefix, "")
        return text

    def extract_raw(self, text: str, html: bool) -> list[str]:
        found: list[str] = []
        if html:
            parser = LinkParser()
            try:
                parser.feed(text)
                found.extend(parser.found)
            except Exception:
                pass
        found.extend(css_references(text))
        decoded = text.replace("\\/", "/")
        for source in (text, decoded):
            found.extend(match.group(1) for match in self.host_url_re.finditer(source))
            found.extend(self.root_asset_re.findall(source))
        return found

    def consider(self, raw: str, base: str) -> tuple[str, str, str] | None:
        item = self.classify(raw, base)
        if not item:
            return None
        kind, url, path = item
        if kind == "asset":
            with self.lock:
                if path not in self.queued_assets:
                    self.queued_assets.add(path)
                    self.asset_jobs[path] = url
        return item

    def page_dest(self, path: str) -> Path:
        relative = path.strip("/")
        if not relative:
            return self.dest / "index.html"
        return self.dest / relative / "index.html"

    def asset_dest(self, path: str) -> Path:
        return self.dest / path.strip("/")

    def inside_dest(self, path: Path) -> bool:
        try:
            path.resolve().relative_to(self.dest.resolve())
        except ValueError:
            return False
        return True

    def atomic_write(self, dest: Path, data: bytes) -> None:
        if not self.inside_dest(dest):
            raise ValueError(f"refusing to write outside mirror: {dest}")
        dest.parent.mkdir(parents=True, exist_ok=True)
        temporary = dest.with_name(dest.name + ".part")
        temporary.write_bytes(data)
        temporary.replace(dest)

    def crawl(self, seeds: list[str]) -> None:
        queue: deque[tuple[str, str]] = deque()
        seen: set[str] = set()
        for seed in seeds:
            item = self.consider(seed, self.origin + "/")
            if item and item[0] == "page" and item[2] not in seen:
                seen.add(item[2])
                queue.append((item[1], item[2]))
        while queue:
            url, path = queue.popleft()
            print(f"  page {path}", flush=True)
            result = fetch(url)
            if result["status"] != 200:
                self.note_error(f"{result['status'] or result['error']} {url}")
                if path == "/":
                    raise SystemExit(f"homepage failed for {self.origin}: {result['error'] or result['status']}")
                continue
            final_path = self.normalize_path(urlparse(result["url"]).path or "/", True)
            if not final_path or urlparse(result["url"]).netloc.lower() != self.host.lower():
                continue
            if self.should_skip(final_path):
                continue
            ctype = result["ctype"].lower()
            if "html" not in ctype:
                self.consider(result["url"], self.origin + "/")
                continue
            if final_path != "/" and not final_path.endswith("/"):
                final_path += "/"
            seen.add(final_path)
            text = result["data"].decode("utf-8", "replace")
            base = self.origin + final_path
            for raw in self.extract_raw(text, html=True):
                item = self.consider(raw, base)
                if item and item[0] == "page" and item[2] not in seen:
                    seen.add(item[2])
                    queue.append((item[1], item[2]))
            self.atomic_write(self.page_dest(final_path), self.rewrite(text).encode("utf-8"))
            self.pages += 1
            if self.pages > 5000:
                self.note_error("stopped after 5000 pages")
                break

    def sitemap_urls(self) -> list[str]:
        result = fetch(self.origin + "/wp-sitemap.xml")
        if result["status"] != 200:
            print("  no sitemap", flush=True)
            return []
        urls: list[str] = []
        pending = [result["data"]]
        seen_maps: set[str] = set()
        while pending:
            blob = pending.pop()
            try:
                root = ElementTree.fromstring(blob)
            except ElementTree.ParseError:
                self.note_error("unreadable sitemap")
                continue
            locs = [node.text.strip() for node in root.iter() if node.tag.rsplit("}", 1)[-1] == "loc" and node.text]
            tag = root.tag.rsplit("}", 1)[-1]
            if tag == "sitemapindex":
                for loc in locs:
                    if loc in seen_maps:
                        continue
                    seen_maps.add(loc)
                    child = fetch(loc)
                    if child["status"] == 200:
                        pending.append(child["data"])
                    else:
                        self.note_error(f"{child['status']} {loc}")
            else:
                urls.extend(locs)
        print(f"  sitemap urls {len(urls)}", flush=True)
        return urls

    def rest_json(self, url: str) -> tuple[dict | list | None, dict]:
        result = fetch(url)
        if result["status"] != 200:
            return None, {}
        import json

        try:
            return json.loads(result["data"].decode("utf-8")), dict(result["headers"])
        except Exception as error:  # noqa: BLE001
            self.note_error(f"bad json {url}: {error}")
            return None, {}

    def rest_collection(self, rest_base: str) -> list[dict]:
        import json

        items: list[dict] = []
        page = 1
        while page < 100:
            url = f"{self.origin}/wp-json/wp/v2/{rest_base}?per_page=100&page={page}"
            result = fetch(url)
            if result["status"] == 400:
                break
            if result["status"] != 200:
                self.note_error(f"{result['status']} {url}")
                break
            try:
                data = json.loads(result["data"].decode("utf-8"))
            except Exception as error:  # noqa: BLE001
                self.note_error(f"bad json {url}: {error}")
                break
            if not isinstance(data, list) or not data:
                break
            items.extend(item for item in data if isinstance(item, dict))
            total_pages = int(result["headers"].get("X-WP-TotalPages") or result["headers"].get("x-wp-totalpages") or page)
            if page >= total_pages:
                break
            page += 1
        return items

    def rest_links(self) -> list[str]:
        types, _headers = self.rest_json(self.origin + "/wp-json/wp/v2/types")
        if not isinstance(types, dict):
            print("  no REST types", flush=True)
            return []
        links: list[str] = []
        for name, info in types.items():
            if name in SKIP_REST_TYPES or name.startswith("wp_"):
                continue
            if not isinstance(info, dict):
                continue
            rest_base = info.get("rest_base")
            if not rest_base:
                continue
            items = self.rest_collection(str(rest_base))
            print(f"  rest {rest_base} {len(items)}", flush=True)
            for item in items:
                link = item.get("link")
                if isinstance(link, str):
                    links.append(link)
        return links

    def media_urls(self) -> list[str]:
        urls: list[str] = []
        for item in self.rest_collection("media"):
            source = item.get("source_url")
            if isinstance(source, str):
                urls.append(source)
            details = item.get("media_details") or {}
            sizes = details.get("sizes") if isinstance(details, dict) else None
            if not isinstance(sizes, dict):
                continue
            for info in sizes.values():
                if not isinstance(info, dict):
                    continue
                sized = info.get("source_url")
                if isinstance(sized, str) and sized:
                    urls.append(sized)
                    continue
                filename = info.get("file")
                if isinstance(filename, str) and isinstance(source, str) and source:
                    parent = source.rsplit("/", 1)[0]
                    urls.append(parent + "/" + filename.split("/")[-1])
        return urls

    def download_assets(self) -> None:
        wave = 0
        while True:
            with self.lock:
                if not self.asset_jobs:
                    break
                jobs = self.asset_jobs
                self.asset_jobs = {}
            wave += 1
            print(f"  asset wave {wave}: {len(jobs)}", flush=True)
            with ThreadPoolExecutor(max_workers=ASSET_WORKERS) as pool:
                futures = [pool.submit(self.download_asset, path, url) for path, url in jobs.items()]
                done = 0
                for future in as_completed(futures):
                    done += 1
                    if done % 50 == 0 or done == len(futures):
                        print(f"    {done}/{len(futures)}", flush=True)
                    try:
                        future.result()
                    except Exception as error:  # noqa: BLE001
                        self.note_error(f"asset worker: {error}")

    def download_asset(self, path: str, url: str) -> None:
        dest = self.asset_dest(path)
        ext = self.extension(path)
        textish = ext in TEXT_EXTENSIONS
        if dest.exists() and dest.stat().st_size > 0 and not textish:
            return
        result = fetch(url)
        if result["status"] != 200 or not result["data"]:
            self.note_error(f"{result['status'] or result['error']} {url}")
            return
        data = result["data"]
        if not self.looks_valid(path, data):
            self.note_error(f"invalid file {url}")
            return
        if textish:
            text = data.decode("utf-8", "replace")
            base = self.origin + path
            if ext == ".css":
                base = self.origin + path.rsplit("/", 1)[0] + "/"
            for raw in self.extract_raw(text, html=ext in {".html", ".htm", ".svg", ".xml"}):
                self.consider(raw, base)
            data = self.rewrite(text).encode("utf-8")
        try:
            self.atomic_write(dest, data)
        except OSError as error:
            self.note_error(f"write {path}: {error}")
            return
        with self.lock:
            self.assets_saved += 1
            if len(data) > GITHUB_FILE_LIMIT:
                self.large.append(f"{len(data) / (1024 * 1024):.1f}MB {path}")

    def looks_valid(self, path: str, data: bytes) -> bool:
        ext = self.extension(path)
        if ext in {".jpg", ".jpeg"}:
            return data.startswith(b"\xff\xd8")
        if ext == ".png":
            return data.startswith(b"\x89PNG")
        if ext == ".gif":
            return data.startswith((b"GIF87", b"GIF89"))
        if ext == ".pdf":
            return data.startswith(b"%PDF")
        if ext == ".webp":
            return len(data) > 12 and data[8:12] == b"WEBP"
        if data.lstrip().startswith(b"<") and ext in {".jpg", ".jpeg", ".png", ".gif", ".pdf", ".webp", ".mp4", ".zip"}:
            return False
        return True

    def summary(self) -> None:
        print(
            f"  done pages={self.pages} assets={self.assets_saved} errors={len(self.errors)}",
            flush=True,
        )
        if self.large:
            print("  files over 100MB (GitHub will reject these):", flush=True)
            for line in self.large:
                print(f"    {line}", flush=True)
        else:
            print("  no files over 100MB", flush=True)
        if self.errors:
            preview = self.errors[:30]
            print(f"  first {len(preview)} errors:", flush=True)
            for line in preview:
                print(f"    {line}", flush=True)


def self_test() -> None:
    main_site = Mirror("https://actionsee.org", "actionsee.org")
    resource = Mirror("https://resource.actionsee.org", "resource.actionsee.org")
    assert main_site.rewrite("https://actionsee.org/news/") == "/news/"
    assert main_site.rewrite("https://actionsee.org/") == "/"
    assert main_site.rewrite("https://resource.actionsee.org/news/") == "https://resource.actionsee.org/news/"
    assert main_site.rewrite("url(//actionsee.org/app/a.png)") == "url(/app/a.png)"
    assert main_site.rewrite("https:\\/\\/actionsee.org\\/news\\/") == "\\/news\\/"
    assert resource.rewrite("https://resource.actionsee.org/albania/") == "/albania/"
    assert resource.rewrite("https://actionsee.org/news/") == "https://actionsee.org/news/"
    assert main_site.classify("https://actionsee.org/news/", main_site.origin + "/") == (
        "page",
        "https://actionsee.org/news/",
        "/news/",
    )
    assert main_site.classify("/app/uploads/a.jpg?ver=1", main_site.origin + "/") == (
        "asset",
        "https://actionsee.org/app/uploads/a.jpg",
        "/app/uploads/a.jpg",
    )
    assert main_site.classify("r", main_site.origin + "/news/") is None
    assert main_site.classify("https://actionsee.org/news/&title=Hello", main_site.origin + "/") == (
        "page",
        "https://actionsee.org/news/",
        "/news/",
    )
    assert main_site.classify("https://actionsee.org/wp-json/", main_site.origin + "/") is None
    assert css_references("a=new Worker(URL.createObjectURL(r),{name:'x'})") == []
    assert main_site.classify("https://actionsee.org/feed/", main_site.origin + "/") is None
    assert main_site.page_dest("/news/") == main_site.dest / "news" / "index.html"
    assert main_site.page_dest("/") == main_site.dest / "index.html"
    assert main_site.page_dest("/2020/02/07/slug/") == main_site.dest / "2020/02/07/slug" / "index.html"
    joined = urljoin(
        "https://actionsee.org/app/themes/ActionSEE/dist/styles/",
        "../images/logo.svg",
    )
    assert joined == "https://actionsee.org/app/themes/ActionSEE/dist/images/logo.svg"
    print("self-test ok")


def selected_sites() -> list[tuple[str, str]]:
    if len(sys.argv) == 1:
        return list(SITES)
    wanted = {arg.rstrip("/") for arg in sys.argv[1:] if arg != "--self-test"}
    chosen = []
    for origin, folder in SITES:
        if origin in wanted or folder in wanted or urlparse(origin).netloc in wanted:
            chosen.append((origin, folder))
    if not chosen:
        raise SystemExit(f"unknown site {sys.argv[1:]}; choose actionsee.org or resource.actionsee.org")
    return chosen


def main() -> None:
    if "--self-test" in sys.argv:
        self_test()
        if len(sys.argv) == 2:
            return
    for origin, folder in selected_sites():
        Mirror(origin, folder).run()


if __name__ == "__main__":
    main()
