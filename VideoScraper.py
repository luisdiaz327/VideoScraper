#!/usr/bin/env python3
"""
VideoScraper Advanced — authorized video discovery/downloader.

Highlights
----------
- yt-dlp first for supported sites and HLS/DASH.
- Selenium fallback for JS-rendered pages.
- BeautifulSoup/static HTML discovery for <video>, <source>, OpenGraph,
  JSON-LD, data-* attributes, and CSS background URLs.
- Recursive iframe discovery with a configurable depth.
- Network/performance-log discovery from Chrome.
- Candidate scoring, deduplication, and optional interactive selection.
- Resume-friendly direct downloads using HTTP Range when supported.
- Atomic ".part" files so interrupted downloads do not masquerade as complete.
- JSON discovery/report export.
- Batch input from repeated --url flags or a text file.
- Per-URL output folders and collision-safe filenames.
- Rate-limited scrolling and request timeout controls.
- Does not implement DRM, paywall, authentication, CAPTCHA, or anti-bot bypass.

Exit codes
----------
0   success
1   invalid input/configuration
2   one or more downloads failed
130 interrupted
"""

from __future__ import annotations

import argparse
import hashlib
import json
import mimetypes
import os
import re
import shutil
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Optional, Set
from urllib.parse import unquote, urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from tqdm import tqdm

try:
    import yt_dlp  # type: ignore
except ImportError:
    yt_dlp = None

from selenium import webdriver
from selenium.webdriver.chrome.options import Options as ChromeOptions
from selenium.webdriver.chrome.service import Service as ChromeService
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.chrome import ChromeDriverManager


USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/126.0.0.0 Safari/537.36"
)

DIRECT_VIDEO_EXTS = (".mp4", ".webm", ".mov", ".m4v", ".mkv", ".avi", ".flv", ".ts")
STREAM_EXTS = (".m3u8", ".mpd")
MEDIA_MIME_HINTS = (
    "video/",
    "application/vnd.apple.mpegurl",
    "application/x-mpegurl",
    "application/dash+xml",
)

PAGE_LOAD_TIMEOUT = 30
DOWNLOAD_TIMEOUT = 60
DOWNLOAD_CHUNK_SIZE = 1024 * 1024
DEFAULT_RETRIES = 3
SCROLL_DELAY = 0.8
DEFAULT_IFRAME_DEPTH = 3
AUTO_DETECT_MIN_SCORE = 70
WATCH_MODE_SECONDS = 15
WATCH_POLL_INTERVAL = 1.0
__version__ = "2.2.0"


@dataclass
class Candidate:
    url: str
    score: int
    source: str
    mime: str = ""
    page_url: str = ""

@dataclass
class DiscoveryReport:
    page_url: str
    title: Optional[str] = None
    description: Optional[str] = None
    candidates: list[Candidate] = field(default_factory=list)

def normalize_url(url: str) -> str:
    url = (url or "").strip()
    if not url:
        raise ValueError("URL is empty.")
    if url.startswith("//"):
        url = "https:" + url
    parsed = urlparse(url)
    if not parsed.scheme:
        url = "https://" + url
        parsed = urlparse(url)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        raise ValueError(f"Invalid URL: {url}")
    return url

def normalize_media_url(url: Optional[str], base_url: Optional[str] = None) -> Optional[str]:
    if not url:
        return None
    value = unquote(str(url)).strip().strip("'\"")
    if not value or value.startswith(("data:", "blob:", "javascript:", "#")):
        return None
    if value.startswith("//"):
        return "https:" + value
    if base_url:
        value = urljoin(base_url, value)
    parsed = urlparse(value)
    return value if parsed.scheme in {"http", "https"} and parsed.netloc else None

def sanitize_filename(name: str, fallback: str = "video") -> str:
    name = unquote(name or "").strip()
    name = re.sub(r"[\\/:*?\"<>|]+", "_", name)
    name = re.sub(r"\s+", " ", name).strip(" ._")
    return (name[:160] or fallback)

def slugify(name: str, fallback: str = "page") -> str:
    value = re.sub(r"[^a-zA-Z0-9._-]+", "-", name.strip().lower())
    return value.strip("-._") or fallback

def unique_path(path: Path) -> Path:
    if not path.exists():
        return path
    for counter in range(2, 10_000):
        candidate = path.with_name(f"{path.stem}_{counter}{path.suffix}")
        if not candidate.exists():
            return candidate
    raise RuntimeError("Could not create a unique output filename.")

def get_url_extension(url: str) -> str:
    path = urlparse(url).path.lower()
    for ext in DIRECT_VIDEO_EXTS + STREAM_EXTS:
        if path.endswith(ext):
            return ext
    return ""

def looks_like_media_url(url: Optional[str], mime: str = "") -> bool:
    if not url:
        return False
    lower = url.lower()
    path = urlparse(url).path.lower()
    m = (mime or "").lower()

    if lower.startswith(("data:", "blob:", "javascript:")):
        return False

    bad = ("thumbnail", "thumb", "sprite", "poster", ".jpg", ".jpeg", ".png", ".gif", ".svg")
    if any(x in lower for x in bad):
        return False

    if path.endswith(DIRECT_VIDEO_EXTS + STREAM_EXTS):
        return True
    if any(x in m for x in MEDIA_MIME_HINTS):
        return True

    # Extensionless CDN/media URLs.
    return any(hint in lower for hint in ("m3u8", "mpd", "manifest", "video.mp4", ".mp4?"))

def score_media_url(url: str, mime: str = "") -> int:
    lower = url.lower()
    path = urlparse(url).path.lower()
    score = 0

    ext_scores = {
        ".mp4": 140, ".webm": 130, ".m3u8": 120, ".mpd": 110,
        ".mov": 100, ".m4v": 100, ".mkv": 90, ".avi": 80, ".flv": 70, ".ts": 60
    }
    score += ext_scores.get(next((e for e in ext_scores if path.endswith(e)), ""), 20)

    for token, pts in (
        (("2160", "4k", "uhd"), 45),
        (("1440",), 38),
        (("1080", "fhd"), 30),
        (("720", "hd"), 20),
    ):
        if any(x in lower for x in token):
            score += pts

    if any(x in lower for x in ("preview", "trailer", "sample", "teaser", "ads", "tracking")):
        score -= 55
    if any(x in lower for x in ("low", "240p", "360p")):
        score -= 15
    if "video/" in (mime or "").lower():
        score += 10
    return score

def dedupe_candidates(candidates: Iterable[Candidate]) -> list[Candidate]:
    best: dict[str, Candidate] = {}
    for item in candidates:
        url = normalize_media_url(item.url, item.page_url)
        if not url or not looks_like_media_url(url, item.mime):
            continue
        current = best.get(url)
        candidate = Candidate(
            url=url,
            score=score_media_url(url, item.mime) + item.score,
            source=item.source,
            mime=item.mime,
            page_url=item.page_url,
        )
        if current is None or candidate.score > current.score:
            best[url] = candidate
    return sorted(best.values(), key=lambda x: x.score, reverse=True)

def request_session(referer: Optional[str] = None) -> requests.Session:
    session = requests.Session()
    session.headers.update({"User-Agent": USER_AGENT, "Accept": "*/*"})
    if referer:
        session.headers["Referer"] = referer
    return session

def extract_metadata(html: str, page_url: str) -> tuple[Optional[str], Optional[str]]:
    soup = BeautifulSoup(html, "html.parser")
    title = (
        soup.title.get_text(" ", strip=True) if soup.title
        else None
    )
    desc = None
    meta = soup.select_one('meta[name="description"]')
    if meta:
        desc = meta.get("content")
    if not desc:
        og = soup.select_one('meta[property="og:description"]')
        if og:
            desc = og.get("content")
    return title, desc

def discover_static_html(page_url: str, html: str) -> list[Candidate]:
    soup = BeautifulSoup(html, "html.parser")
    found: list[Candidate] = []

    def add(value: Optional[str], source: str, mime: str = "", bonus: int = 0):
        url = normalize_media_url(value, page_url)
        if url and looks_like_media_url(url, mime):
            found.append(Candidate(url, bonus, source, mime, page_url))

    # <video src>, <video poster> is intentionally ignored, <source src>.
    for video in soup.select("video"):
        add(video.get("src"), "html:video", video.get("type", ""), 25)
        for source in video.select("source"):
            add(source.get("src"), "html:source", source.get("type", ""), 30)

    for source in soup.select("source[src]"):
        add(source.get("src"), "html:source", source.get("type", ""), 20)

    # Common media-related attributes.
    attrs = (
        "src", "data-src", "data-video", "data-video-url", "data-file",
        "data-media", "data-media-url", "data-stream", "data-hls", "data-mp4",
        "data-url", "data-playback-url"
    )
    for attr in attrs:
        for tag in soup.select(f"[{attr}]"):
            add(tag.get(attr), f"html:{attr}", tag.get("type", ""), 12)

    # OpenGraph / Twitter cards can expose a usable media URL.
    for selector, source in (
        ('meta[property="og:video"]', "meta:og:video"),
        ('meta[property="og:video:url"]', "meta:og:video:url"),
        ('meta[property="og:video:secure_url"]', "meta:og:video:secure_url"),
        ('meta[name="twitter:player:stream"]', "meta:twitter:player:stream"),
    ):
        tag = soup.select_one(selector)
        if tag:
            add(tag.get("content"), source, tag.get("content-type", ""), 18)

    # JSON-LD can contain contentUrl / embedUrl.
    for script in soup.select('script[type="application/ld+json"]'):
        text = script.string or script.get_text()
        if not text.strip():
            continue
        try:
            payload = json.loads(text)
        except Exception:
            continue

        def walk(obj):
            if isinstance(obj, dict):
                for key in ("contentUrl", "embedUrl", "url"):
                    val = obj.get(key)
                    if isinstance(val, str):
                        add(val, f"jsonld:{key}", "", 14)
                for val in obj.values():
                    walk(val)
            elif isinstance(obj, list):
                for val in obj:
                    walk(val)

        walk(payload)

    # CSS background-image: url(...)
    for tag in soup.select("[style]"):
        style = tag.get("style", "")
        for match in re.finditer(r"url\((.*?)\)", style, re.I):
            value = match.group(1).strip().strip("'\"")
            add(value, "css:background", "", 8)

    return found

def create_chrome_driver(headless: bool = True) -> webdriver.Chrome:
    options = ChromeOptions()
    if headless:
        options.add_argument("--headless=new")
    options.add_argument("--window-size=1440,1000")
    options.add_argument("--autoplay-policy=no-user-gesture-required")
    options.add_argument("--disable-notifications")
    options.add_argument("--disable-popup-blocking")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument(f"--user-agent={USER_AGENT}")
    options.set_capability("goog:loggingPrefs", {"performance": "ALL", "browser": "ALL"})

    driver = webdriver.Chrome(
        service=ChromeService(ChromeDriverManager().install()),
        options=options,
    )
    try:
        driver.execute_cdp_cmd("Network.enable", {})
    except Exception:
        pass
    return driver

def wait_for_page(driver: webdriver.Chrome, timeout: int = PAGE_LOAD_TIMEOUT) -> None:
    WebDriverWait(driver, timeout).until(
        lambda d: d.execute_script(
            "return document.readyState"
        ) in {"interactive", "complete"}
    )
    time.sleep(1.5)

def collect_dom_media_urls_in_current_frame(
    driver: webdriver.Chrome, page_url: str
) -> list[Candidate]:
    found: list[Candidate] = []

    def add(value: Optional[str], source: str, mime: str = "", bonus: int = 0):
        url = normalize_media_url(value, page_url)
        if url and looks_like_media_url(url, mime):
            found.append(Candidate(url, bonus, source, mime, page_url))

    for video in driver.find_elements(By.TAG_NAME, "video"):
        try:
            add(video.get_attribute("currentSrc"), "dom:video.currentSrc", "", 35)
            add(video.get_attribute("src"), "dom:video.src", "", 28)
            for source in video.find_elements(By.TAG_NAME, "source"):
                add(source.get_attribute("src"), "dom:source", source.get_attribute("type") or "", 32)
        except Exception:
            pass

    for source in driver.find_elements(By.CSS_SELECTOR, "source[src]"):
        try:
            add(source.get_attribute("src"), "dom:source", source.get_attribute("type") or "", 25)
        except Exception:
            pass

    attrs = (
        "src", "data-src", "data-video", "data-video-url", "data-file",
        "data-media", "data-media-url", "data-stream", "data-hls", "data-mp4",
        "data-url", "data-playback-url"
    )
    css = ",".join(f"[{a}]" for a in attrs)

    try:
        for el in driver.find_elements(By.CSS_SELECTOR, css):
            for attr in attrs:
                try:
                    value = el.get_attribute(attr)
                    add(value, f"dom:{attr}", el.get_attribute("type") or "", 15)
                except Exception:
                    pass
    except Exception:
        pass

    return found

def collect_dom_media_urls(
    driver: webdriver.Chrome,
    page_url: str,
    max_depth: int = DEFAULT_IFRAME_DEPTH,
) -> list[Candidate]:
    found: list[Candidate] = []

    def scan(depth: int):
        found.extend(collect_dom_media_urls_in_current_frame(driver, page_url))
        if depth >= max_depth:
            return

        frames = driver.find_elements(By.TAG_NAME, "iframe")
        for index in range(len(frames)):
            try:
                current = driver.find_elements(By.TAG_NAME, "iframe")
                driver.switch_to.frame(current[index])
                scan(depth + 1)
            except Exception:
                pass
            finally:
                try:
                    driver.switch_to.parent_frame()
                except Exception:
                    pass

    driver.switch_to.default_content()
    scan(0)
    driver.switch_to.default_content()
    return found

def collect_network_media_urls(driver: webdriver.Chrome, page_url: str) -> list[Candidate]:
    found: list[Candidate] = []
    try:
        logs = driver.get_log("performance")
    except Exception as exc:
        print(f"⚠️ Could not read Chrome performance logs: {exc}")
        return found

    for entry in logs:
        try:
            message = json.loads(entry["message"]).get("message", {})
            method = message.get("method", "")
            params = message.get("params", {})
            url = None
            mime = ""

            if method == "Network.requestWillBeSent":
                url = params.get("request", {}).get("url")
            elif method == "Network.responseReceived":
                response = params.get("response", {})
                url = response.get("url")
                mime = response.get("mimeType", "")

            if looks_like_media_url(url, mime):
                found.append(
                    Candidate(
                        url=normalize_media_url(url, page_url) or "",
                        score=42,
                        source=f"network:{method}",
                        mime=mime,
                        page_url=page_url,
                    )
                )
        except Exception:
            continue
    return found

def analyze_player_state(driver: webdriver.Chrome) -> dict:
    """Inspect the rendered page for player/stream characteristics.

    This is descriptive analysis only: it does not bypass authentication,
    DRM, CAPTCHA, paywalls, or other access controls.
    """
    result = {
        "video_elements": 0,
        "audio_elements": 0,
        "iframes": 0,
        "native_html5": False,
        "hls_hints": 0,
        "dash_hints": 0,
        "player_frameworks": [],
        "autoplaying": 0,
        "ready_videos": 0,
    }

    try:
        result["video_elements"] = len(driver.find_elements(By.TAG_NAME, "video"))
        result["audio_elements"] = len(driver.find_elements(By.TAG_NAME, "audio"))
        result["iframes"] = len(driver.find_elements(By.TAG_NAME, "iframe"))
    except Exception:
        pass

    try:
        state = driver.execute_script(
            """
            const videos = [...document.querySelectorAll('video')];
            const sources = [
                ...videos.map(v => v.currentSrc || v.src || ''),
                ...document.querySelectorAll('source[src]').values()
                    ? [...document.querySelectorAll('source[src]')].map(s => s.src || s.getAttribute('src') || '')
                    : []
            ];
            const text = document.documentElement.innerHTML.toLowerCase();

            return {
                native: videos.length > 0,
                hls: (text.match(/(?:\\.m3u8|application\\/vnd\\.apple\\.mpegurl|hls\\.js)/g) || []).length,
                dash: (text.match(/(?:\\.mpd|dash\\.js|application\\/dash\\+xml)/g) || []).length,
                autoplaying: videos.filter(v => !v.paused && !v.ended && v.readyState >= 2).length,
                ready: videos.filter(v => v.readyState >= 2).length,
                sources: sources.slice(0, 50)
            };
            """
        ) or {}
        result["native_html5"] = bool(state.get("native"))
        result["hls_hints"] = int(state.get("hls", 0))
        result["dash_hints"] = int(state.get("dash", 0))
        result["autoplaying"] = int(state.get("autoplaying", 0))
        result["ready_videos"] = int(state.get("ready", 0))

        html = driver.page_source.lower()
        framework_map = {
            "video.js": "video.js",
            "plyr": "Plyr",
            "jwplayer": "JW Player",
            "flowplayer": "Flowplayer",
            "bitmovin": "Bitmovin",
            "vimeo": "Vimeo",
            "youtube": "YouTube",
            "mediaelement": "MediaElement",
        }
        result["player_frameworks"] = [
            label for needle, label in framework_map.items() if needle in html
        ]
    except Exception:
        pass

    return result


def print_player_analysis(info: dict) -> None:
    print("\n🧠 SMART PLAYER ANALYZER")
    print("   ─────────────────────────")
    print(f"   HTML5 video      : {'yes' if info.get('native_html5') else 'no'}")
    print(f"   Video elements   : {info.get('video_elements', 0)}")
    print(f"   Iframes          : {info.get('iframes', 0)}")
    print(f"   HLS hints        : {info.get('hls_hints', 0)}")
    print(f"   DASH hints       : {info.get('dash_hints', 0)}")
    print(f"   Ready videos     : {info.get('ready_videos', 0)}")
    print(f"   Playing videos   : {info.get('autoplaying', 0)}")
    frameworks = info.get("player_frameworks") or []
    print(f"   Player frameworks: {', '.join(frameworks) if frameworks else 'not identified'}")


def collect_watch_snapshot(driver: webdriver.Chrome, page_url: str) -> list[Candidate]:
    """Collect a fresh DOM + network snapshot during Watch Mode."""
    found: list[Candidate] = []
    try:
        found.extend(collect_dom_media_urls(driver, page_url, max_depth=DEFAULT_IFRAME_DEPTH))
    except Exception:
        pass
    try:
        found.extend(collect_network_media_urls(driver, page_url))
    except Exception:
        pass
    return dedupe_candidates(found)


def watch_for_media(
    driver: webdriver.Chrome,
    page_url: str,
    duration: int = WATCH_MODE_SECONDS,
    poll_interval: float = WATCH_POLL_INTERVAL,
) -> tuple[list[Candidate], dict]:
    """Watch a rendered page for newly appearing playable media."""
    print(f"\n👀 WATCH MODE — monitoring for up to {duration}s...")
    start = time.monotonic()
    seen: dict[str, Candidate] = {}
    last_analysis_at = 0.0
    analysis = {}

    while time.monotonic() - start < max(1, duration):
        gently_trigger_video_loading(driver, scroll_steps=2)

        for candidate in collect_watch_snapshot(driver, page_url):
            seen[candidate.url] = candidate

        now = time.monotonic()
        if now - last_analysis_at >= 3:
            analysis = analyze_player_state(driver)
            last_analysis_at = now
            print(
                f"   ⏱ {int(now - start):>2}s | "
                f"candidates={len(seen)} | "
                f"videos={analysis.get('video_elements', 0)} | "
                f"playing={analysis.get('autoplaying', 0)}"
            )

        time.sleep(max(0.2, poll_interval))

    final = sorted(seen.values(), key=lambda c: c.score, reverse=True)
    print(f"✅ Watch Mode finished: {len(final)} unique candidate(s) observed.")
    return final, analysis


def gently_trigger_video_loading(driver: webdriver.Chrome, scroll_steps: int = 6) -> None:
    try:
        driver.execute_script(
            """
            document.querySelectorAll('video').forEach(v => {
                try {
                    v.muted = true;
                    v.preload = 'auto';
                    v.load();
                    v.play().catch(() => {});
                } catch (_) {}
            });
            """
        )
    except Exception:
        pass

    try:
        height = driver.execute_script(
            "return Math.max(document.body.scrollHeight, document.documentElement.scrollHeight);"
        )
        if height <= 0:
            return
        positions = [
            int(height * i / max(1, scroll_steps - 1))
            for i in range(scroll_steps)
        ]
        for y in positions:
            driver.execute_script("window.scrollTo(0, arguments[0]);", y)
            time.sleep(SCROLL_DELAY)
        driver.execute_script("window.scrollTo(0, 0);")
    except Exception:
        pass

def fetch_static_page(page_url: str, timeout: int = DOWNLOAD_TIMEOUT) -> tuple[str, str]:
    session = request_session(page_url)
    response = session.get(page_url, timeout=timeout)
    response.raise_for_status()
    return response.text, response.url

def discover_with_selenium(
    page_url: str,
    wait_seconds: int,
    timeout: int,
    headless: bool,
    iframe_depth: int,
    scroll_steps: int,
    watch_mode: bool = False,
    watch_seconds: int = WATCH_MODE_SECONDS,
    watch_interval: float = WATCH_POLL_INTERVAL,
) -> DiscoveryReport:
    driver = create_chrome_driver(headless=headless)
    try:
        print("🌐 Opening page with Selenium...")
        driver.get(page_url)
        wait_for_page(driver, timeout)

        title = driver.title or None
        gently_trigger_video_loading(driver, scroll_steps=scroll_steps)
        time.sleep(max(0, wait_seconds))

        candidates = []
        candidates.extend(collect_dom_media_urls(driver, page_url, iframe_depth))
        candidates.extend(collect_network_media_urls(driver, page_url))

        if watch_mode:
            print_player_analysis(analyze_player_state(driver))
            watched_candidates, watch_analysis = watch_for_media(
                driver,
                page_url,
                duration=watch_seconds,
                poll_interval=watch_interval,
            )
            candidates.extend(watched_candidates)
            print_player_analysis(watch_analysis)

        # Capture the rendered DOM for another parsing pass.
        try:
            rendered_html = driver.page_source
            candidates.extend(discover_static_html(page_url, rendered_html))
        except Exception:
            pass

        return DiscoveryReport(
            page_url=page_url,
            title=title,
            candidates=dedupe_candidates(candidates),
        )
    finally:
        driver.quit()

def discover(
    page_url: str,
    use_selenium: bool = True,
    wait_seconds: int = 6,
    timeout: int = PAGE_LOAD_TIMEOUT,
    headless: bool = True,
    iframe_depth: int = DEFAULT_IFRAME_DEPTH,
    scroll_steps: int = 6,
    watch_mode: bool = False,
    watch_seconds: int = WATCH_MODE_SECONDS,
    watch_interval: float = WATCH_POLL_INTERVAL,
) -> DiscoveryReport:
    candidates: list[Candidate] = []
    title = None
    description = None

    try:
        html, final_url = fetch_static_page(page_url, timeout=timeout)
        title, description = extract_metadata(html, final_url)
        candidates.extend(discover_static_html(final_url, html))
        page_url = final_url
        print(f"🧩 Static HTML discovery: {len(candidates)} candidate(s)")
    except Exception as exc:
        print(f"⚠️ Static HTML discovery failed: {exc}")

    if use_selenium:
        try:
            rendered = discover_with_selenium(
                page_url,
                wait_seconds=wait_seconds,
                timeout=timeout,
                headless=headless,
                iframe_depth=iframe_depth,
                scroll_steps=scroll_steps,
                watch_mode=watch_mode,
                watch_seconds=watch_seconds,
                watch_interval=watch_interval,
            )
            candidates.extend(rendered.candidates)
            title = title or rendered.title
        except Exception as exc:
            print(f"⚠️ Selenium discovery failed: {exc}")

    final = dedupe_candidates(candidates)
    print(f"✅ Total unique media candidates: {len(final)}")
    return DiscoveryReport(
        page_url=page_url,
        title=title,
        description=description,
        candidates=final,
    )

def try_ytdlp_download(
    url: str,
    out_dir: Path,
    quality: str = "best",
    referer: Optional[str] = None,
    quiet: bool = False,
    verbose: bool = False,
) -> bool:
    if yt_dlp is None:
        print("⚠️ yt-dlp is not installed. Skipping yt-dlp.")
        return False

    out_dir.mkdir(parents=True, exist_ok=True)
    ydl_opts = {
        "outtmpl": str(out_dir / "%(title).160B [%(id)s].%(ext)s"),
        "format": quality,
        "noplaylist": True,
        "retries": 5,
        "fragment_retries": 5,
        "continuedl": True,
        "overwrites": False,
        "merge_output_format": "mp4",
        "quiet": quiet and not verbose,
        "no_warnings": not verbose,
        "http_headers": {
            "User-Agent": USER_AGENT,
            **({"Referer": referer} if referer else {}),
        },
    }

    try:
        print("🔎 Trying yt-dlp...")
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            return ydl.download([url]) == 0
    except Exception as exc:
        print(f"⚠️ yt-dlp failed: {exc}")
        return False

def filename_from_candidate(
    page_url: str,
    media_url: str,
    out_dir: Path,
    title: Optional[str] = None,
) -> Path:
    page_name = Path(urlparse(page_url).path.rstrip("/")).name or "video"
    base = sanitize_filename(title or Path(page_name).stem or "video")
    ext = get_url_extension(media_url)

    if ext in STREAM_EXTS or not ext:
        ext = ".mp4"

    # Add a short URL hash to avoid collisions from extensionless CDN URLs.
    token = hashlib.sha1(media_url.encode("utf-8")).hexdigest()[:8]
    return unique_path(out_dir / f"{base} [{token}]{ext}")

def direct_download(
    media_url: str,
    out_path: Path,
    referer: Optional[str],
    retries: int,
    resume: bool = True,
) -> bool:
    session = request_session(referer)
    part = out_path.with_suffix(out_path.suffix + ".part")
    existing = part.stat().st_size if part.exists() else 0

    for attempt in range(1, max(1, retries) + 1):
        try:
            headers = {}
            if resume and existing > 0:
                headers["Range"] = f"bytes={existing}-"

            with session.get(
                media_url,
                headers=headers,
                stream=True,
                timeout=DOWNLOAD_TIMEOUT,
                allow_redirects=True,
            ) as response:
                response.raise_for_status()

                # A server may ignore Range and send the whole file.
                append = existing > 0 and response.status_code == 206
                if not append:
                    existing = 0

                total = response.headers.get("Content-Length")
                if total is not None:
                    total = int(total) + existing if append else int(total)

                mode = "ab" if append else "wb"
                print(f"⬇️ {media_url}")
                print(f"💾 {out_path}")

                with open(part, mode) as fh, tqdm(
                    total=total,
                    initial=existing,
                    unit="B",
                    unit_scale=True,
                    unit_divisor=1024,
                    desc="📥 Progress",
                ) as bar:
                    for chunk in response.iter_content(chunk_size=DOWNLOAD_CHUNK_SIZE):
                        if not chunk:
                            continue
                        fh.write(chunk)
                        bar.update(len(chunk))

            part.replace(out_path)
            print("✅ Direct download complete.")
            return True

        except KeyboardInterrupt:
            raise
        except Exception as exc:
            print(f"⚠️ Attempt {attempt}/{retries} failed: {exc}")
            if attempt < retries:
                time.sleep(2 * attempt)
                existing = part.stat().st_size if part.exists() else 0
            else:
                print("❌ Direct download failed.")
    return False

def save_report(report: DiscoveryReport, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "page_url": report.page_url,
        "title": report.title,
        "description": report.description,
        "candidates": [asdict(x) for x in report.candidates],
        "version": __version__,
        "generated_at": int(time.time()),
    }
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, ensure_ascii=False)
    print(f"📝 Discovery report saved: {path}")

def auto_detect_candidate(
    candidates: list[Candidate],
    min_score: int = AUTO_DETECT_MIN_SCORE,
) -> Optional[Candidate]:
    """Automatically select the strongest candidate.

    Candidates are already deduplicated and score-sorted. Auto mode additionally
    filters obviously weak/preview-like candidates and reports the decision.
    """
    if not candidates:
        print("❌ Auto Detect: no media candidates found.")
        return None

    strong = [c for c in candidates if c.score >= min_score]

    # Prefer non-preview media where possible. The global scorer already applies
    # penalties, but this gives Auto Detect an additional safety net.
    non_preview = [
        c for c in strong
        if not any(
            token in c.url.lower()
            for token in ("preview", "trailer", "sample", "teaser")
        )
    ]

    pool = non_preview or strong or candidates
    chosen = max(pool, key=lambda c: c.score)

    print("\n🤖 AUTO DETECT MODE")
    print(f"   Candidates found : {len(candidates)}")
    print(f"   Strong candidates: {len(strong)}")
    print(f"   Selected score   : {chosen.score}")
    print(f"   Detection source : {chosen.source}")
    print(f"   Media URL        : {chosen.url}")

    if chosen.mime:
        print(f"   MIME             : {chosen.mime}")

    return chosen


def choose_candidate(candidates: list[Candidate], interactive: bool) -> Optional[Candidate]:
    if not candidates:
        return None

    print("\n🎥 Discovered media:")
    for index, item in enumerate(candidates[:30], 1):
        print(f"{index:>2}. score={item.score:<4} source={item.source:<22} {item.url}")

    if not interactive:
        print(f"\n🎯 Auto-selected: {candidates[0].url}")
        return candidates[0]

    while True:
        raw = input("\nSelect candidate number (Enter = best, q = cancel): ").strip().lower()
        if raw == "":
            return candidates[0]
        if raw == "q":
            return None
        try:
            selected = int(raw)
            if 1 <= selected <= min(30, len(candidates)):
                return candidates[selected - 1]
        except ValueError:
            pass
        print("❌ Invalid selection.")

def build_job_dir(out_root: Path, page_url: str, title: Optional[str]) -> Path:
    hostname = slugify(urlparse(page_url).netloc, "site")
    name = slugify(title or Path(urlparse(page_url).path).stem or "video")
    return out_root / hostname / name

def read_url_file(path: Path) -> list[str]:
    urls: list[str] = []
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            urls.append(line)
    return urls

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Advanced authorized video discovery/downloader."
    )
    parser.add_argument("url", nargs="?", help="Single video page URL")
    parser.add_argument(
        "--url", dest="urls", action="append", default=[],
        help="Additional URL; can be supplied more than once."
    )
    parser.add_argument("--input-file", type=Path, help="Text file containing one URL per line")
    parser.add_argument("-o", "--out-dir", type=Path, default=Path("downloads"))
    parser.add_argument("-q", "--quality", default="best", help="yt-dlp format selector")
    parser.add_argument("--no-ytdlp", action="store_true", help="Skip yt-dlp direct extraction")
    parser.add_argument("--no-selenium", action="store_true", help="Skip Selenium fallback")
    parser.add_argument("--list-only", action="store_true", help="Discover/list candidates only")
    parser.add_argument(
        "--auto-detect",
        action="store_true",
        help="Automatically detect and select the strongest media candidate",
    )
    parser.add_argument("--interactive", action="store_true", help="Choose a media candidate interactively")
    parser.add_argument(
        "--min-score",
        type=int,
        default=AUTO_DETECT_MIN_SCORE,
        help=f"Minimum score preferred by --auto-detect (default: {AUTO_DETECT_MIN_SCORE})",
    )
    parser.add_argument("--headful", action="store_true", help="Show Chrome window")
    parser.add_argument("--wait", type=int, default=6, help="Extra wait for lazy media")
    parser.add_argument("--timeout", type=int, default=PAGE_LOAD_TIMEOUT)
    parser.add_argument("--retries", type=int, default=DEFAULT_RETRIES)
    parser.add_argument("--iframe-depth", type=int, default=DEFAULT_IFRAME_DEPTH)
    parser.add_argument("--scroll-steps", type=int, default=6)
    parser.add_argument(
        "--watch",
        "--watch-mode",
        dest="watch_mode",
        action="store_true",
        help="Continuously watch the rendered player for late-appearing media",
    )
    parser.add_argument(
        "--watch-seconds",
        type=int,
        default=WATCH_MODE_SECONDS,
        help=f"Watch duration in seconds (default: {WATCH_MODE_SECONDS})",
    )
    parser.add_argument(
        "--watch-interval",
        type=float,
        default=WATCH_POLL_INTERVAL,
        help=f"Watch polling interval in seconds (default: {WATCH_POLL_INTERVAL})",
    )
    parser.add_argument("--resume", action="store_true", help="Resume interrupted direct downloads")
    parser.add_argument("--report", type=Path, help="Save a discovery JSON report")
    parser.add_argument("--report-all", action="store_true", help="Save one JSON report beside each job")
    parser.add_argument("--version", action="version", version=f"%(prog)s {__version__}")

    args = parser.parse_args()

    urls = []
    if args.url:
        urls.append(args.url)
    urls.extend(args.urls)
    if args.input_file:
        urls.extend(read_url_file(args.input_file))

    if not urls:
        raw = input("🔗 Enter video page URL: ").strip()
        if raw:
            urls.append(raw)

    if not urls:
        print("❌ No URL provided.")
        return 1

    normalized = []
    for raw in urls:
        try:
            normalized.append(normalize_url(raw))
        except ValueError as exc:
            print(f"❌ Skipping invalid URL: {exc}")

    if not normalized:
        return 1

    success = 0
    failures = 0

    print(f"🎬 VideoScraper Advanced v{__version__}")
    print(f"📦 Jobs: {len(normalized)}")
    if args.auto_detect:
        print(f"🤖 Mode: AUTO DETECT (minimum preferred score: {args.min_score})")
    if args.watch_mode:
        print(
            f"👀 Mode: WATCH ({max(1, args.watch_seconds)}s, "
            f"{max(0.2, args.watch_interval):g}s polling)"
        )
    print("⚠️ Use only for content you are authorized to access/download.\n")

    for job_index, page_url in enumerate(normalized, 1):
        print("=" * 78)
        print(f"🚀 Job {job_index}/{len(normalized)}: {page_url}")

        try:
            # Stage 1: yt-dlp, when available. Auto Detect keeps this as the
            # first attempt because yt-dlp can resolve site-specific players,
            # playlists, formats, HLS, and DASH without manual candidate selection.
            job_title = None
            if not args.no_ytdlp and not args.list_only:
                job_dir = args.out_dir / slugify(urlparse(page_url).netloc, "site")
                if try_ytdlp_download(
                    page_url,
                    job_dir,
                    quality=args.quality,
                    referer=page_url,
                    verbose=True,
                ):
                    print("✅ Finished with yt-dlp.")
                    success += 1
                    continue

            # Stage 2: HTML + Selenium discovery.
            report = discover(
                page_url,
                use_selenium=not args.no_selenium,
                wait_seconds=args.wait,
                timeout=args.timeout,
                headless=not args.headful,
                iframe_depth=max(0, args.iframe_depth),
                scroll_steps=max(1, args.scroll_steps),
                watch_mode=args.watch_mode,
                watch_seconds=max(1, args.watch_seconds),
                watch_interval=max(0.2, args.watch_interval),
            )
            job_title = report.title
            job_dir = build_job_dir(args.out_dir, report.page_url, job_title)
            job_dir.mkdir(parents=True, exist_ok=True)

            report_path = args.report
            if args.report_all:
                report_path = job_dir / "discovery.json"
            if report_path:
                if len(normalized) > 1 and not args.report_all and report_path.suffix:
                    report_path = report_path.with_name(
                        f"{report_path.stem}_{job_index}{report_path.suffix}"
                    )
                save_report(report, report_path)

            if args.list_only:
                success += 1
                continue

            if args.auto_detect:
                chosen = auto_detect_candidate(report.candidates, min_score=args.min_score)
            else:
                chosen = choose_candidate(report.candidates, args.interactive)

            if chosen is None:
                print("⚠️ No candidate selected/detected.")
                failures += 1
                continue

            # HLS/DASH is handed to yt-dlp rather than treating the manifest as MP4 bytes.
            if get_url_extension(chosen.url) in STREAM_EXTS:
                if try_ytdlp_download(
                    chosen.url,
                    job_dir,
                    quality=args.quality,
                    referer=report.page_url,
                    verbose=True,
                ):
                    success += 1
                    continue
                print("❌ Stream download failed via yt-dlp.")
                failures += 1
                continue

            output = filename_from_candidate(
                report.page_url,
                chosen.url,
                job_dir,
                title=job_title,
            )

            if direct_download(
                chosen.url,
                output,
                referer=report.page_url,
                retries=args.retries,
                resume=args.resume,
            ):
                success += 1
            else:
                failures += 1

        except KeyboardInterrupt:
            print("\n🛑 Interrupted by user.")
            return 130
        except Exception as exc:
            failures += 1
            print(f"❌ Job failed: {exc}")

    print("\n" + "=" * 78)
    print(f"✅ Successful: {success}")
    print(f"❌ Failed:     {failures}")
    return 0 if failures == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
