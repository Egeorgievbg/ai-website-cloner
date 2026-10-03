#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, os, re, time
from collections import deque
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional
from urllib.parse import parse_qsl, urlencode, urljoin, urlparse, urlunparse
from urllib.robotparser import RobotFileParser
import xml.etree.ElementTree as ET
import requests
from bs4 import BeautifulSoup

UA = "TechnicalArchiveBot/1.0 (+technical audit; polite crawler)"
HTML_TYPES = {"text/html", "application/xhtml+xml"}
SKIP_PREFIXES = ("/wp-admin","/wp-login","/xmlrpc.php","/cart","/checkout","/my-account","/login","/logout","/admin","/api/","/feed","/comments/feed")
SKIP_EXTENSIONS = {".jpg",".jpeg",".png",".webp",".gif",".svg",".ico",".pdf",".zip",".mp4",".webm",".mp3",".wav",".woff",".woff2",".ttf",".otf",".eot",".js",".mjs",".json",".xml",".txt",".rss",".atom"}
CSS_IMPORT_RE = re.compile(r"@import\s+(?:url\()?\s*['\"]?([^'\")\s;]+)", re.I)

@dataclass
class Entry:
    url: str
    final_url: str
    status: Optional[int]
    content_type: str
    kind: str
    local_path: Optional[str]
    bytes: int
    sha256: Optional[str]
    elapsed_ms: Optional[int]
    error: Optional[str] = None

def now_iso(): return datetime.now(timezone.utc).isoformat()

def normalize_url(url, keep_query=False):
    p=urlparse(url); scheme=(p.scheme or "https").lower(); host=(p.hostname or "").lower(); port=p.port
    netloc=host
    if port and not ((scheme=="https" and port==443) or (scheme=="http" and port==80)): netloc=f"{host}:{port}"
    path=p.path or "/"; query=""
    if keep_query and p.query: query=urlencode(sorted(parse_qsl(p.query, keep_blank_values=True)))
    return urlunparse((scheme,netloc,path,"",query,""))

def origin(url):
    p=urlparse(url); return p.scheme.lower(), (p.hostname or "").lower(), p.port

def same_origin(a,b): return origin(a)==origin(b)

def slug_for_url(url, ext):
    p=urlparse(url); host=p.hostname or "unknown-host"; path=p.path or "/"
    if path.endswith("/"): path += "index"
    name=Path(path.lstrip("/"))
    if not name.suffix: name=name.with_suffix(ext)
    elif name.suffix.lower()!=ext: name=Path(str(name)+ext)
    if p.query:
        digest=hashlib.sha1(p.query.encode()).hexdigest()[:10]
        name=name.with_name(f"{name.stem}__q_{digest}{name.suffix}")
    return Path(host)/name

def safe_write(root, rel, data):
    dest=root/rel; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data); return str(rel).replace(os.sep,"/")

def sha256(data): return hashlib.sha256(data).hexdigest()
def content_type(resp): return resp.headers.get("content-type","").split(";",1)[0].strip().lower()

def looks_like_html_url(url):
    p=urlparse(url); low=p.path.lower()
    if any(low.startswith(x) for x in SKIP_PREFIXES): return False
    if Path(low).suffix in SKIP_EXTENSIONS: return False
    return p.scheme in {"http","https"}

def discover_sitemaps(session, base, timeout):
    p=urlparse(base); root=f"{p.scheme}://{p.netloc}"; candidates=[f"{root}/sitemap.xml",f"{root}/sitemap_index.xml"]
    try:
        r=session.get(f"{root}/robots.txt",timeout=timeout,allow_redirects=True)
        if r.ok:
            for line in r.text.splitlines():
                if line.lower().startswith("sitemap:"): candidates.append(line.split(":",1)[1].strip())
    except requests.RequestException: pass
    out=[]; seen=set()
    for u in candidates:
        u=normalize_url(u,keep_query=True)
        if u not in seen: seen.add(u); out.append(u)
    return out

def parse_sitemap(session, sitemap_url, timeout, depth=0):
    if depth>4: return set()
    urls=set()
    try:
        r=session.get(sitemap_url,timeout=timeout,allow_redirects=True)
        if not r.ok: return urls
        root=ET.fromstring(r.content)
    except Exception: return urls
    nsless=lambda t: t.split("}")[-1].lower()
    if nsless(root.tag)=="sitemapindex":
        for el in root.iter():
            if nsless(el.tag)=="loc" and el.text: urls |= parse_sitemap(session,el.text.strip(),timeout,depth+1)
    else:
        for el in root.iter():
            if nsless(el.tag)=="loc" and el.text: urls.add(el.text.strip())
    return urls

def build_robot_parser(session, base, timeout):
    p=urlparse(base); robots_url=f"{p.scheme}://{p.netloc}/robots.txt"; rp=RobotFileParser(); rp.set_url(robots_url)
    try:
        r=session.get(robots_url,timeout=timeout)
        rp.parse(r.text.splitlines() if r.ok else [])
    except requests.RequestException: rp.parse([])
    return rp

class Archiver:
    def __init__(self, site, out, delay, timeout, max_pages, obey_robots, keep_query):
        self.site=normalize_url(site,keep_query=keep_query); self.out=out; self.delay=max(delay,0); self.timeout=timeout; self.max_pages=max_pages
        self.obey_robots=obey_robots; self.keep_query=keep_query; self.session=requests.Session()
        self.session.headers.update({"User-Agent":UA,"Accept":"text/html,application/xhtml+xml,text/css,*/*;q=0.8"})
        self.entries=[]; self.seen_pages=set(); self.seen_css=set(); self.queue=deque(); self.robot=build_robot_parser(self.session,self.site,self.timeout)
        self.main_origin=origin(self.site); self.external_css_hosts=set()

    def allowed(self,url): return (not self.obey_robots) or self.robot.can_fetch(UA,url)

    def get(self,url):
        if self.delay: time.sleep(self.delay)
        start=time.perf_counter()
        try:
            r=self.session.get(url,timeout=self.timeout,allow_redirects=True)
            r._archive_elapsed_ms=int((time.perf_counter()-start)*1000)
            return r
        except requests.RequestException as e:
            self.entries.append(Entry(url,url,None,"","error",None,0,None,None,repr(e))); return None

    def save_response(self,requested_url,r,kind,ext):
        final_url=normalize_url(r.url,keep_query=self.keep_query); rel=Path("raw")/kind/slug_for_url(final_url,ext)
        local=safe_write(self.out,rel,r.content)
        self.entries.append(Entry(requested_url,final_url,r.status_code,content_type(r),kind,local,len(r.content),sha256(r.content),getattr(r,"_archive_elapsed_ms",None),None))
        headers_rel=Path("headers")/kind/slug_for_url(final_url,ext+".headers.json")
        safe_write(self.out,headers_rel,json.dumps(dict(r.headers),ensure_ascii=False,indent=2).encode())
        return local

    def enqueue_page(self,url):
        u=normalize_url(url,keep_query=self.keep_query)
        if same_origin(u,self.site) and looks_like_html_url(u) and u not in self.seen_pages: self.queue.append(u)

    def discover_html(self,page_url,html):
        soup=BeautifulSoup(html,"lxml")
        for tag in soup.find_all("a",href=True):
            href=tag.get("href","").strip()
            if href and not href.startswith(("mailto:","tel:","javascript:","data:")): self.enqueue_page(urljoin(page_url,href))
        for tag in soup.find_all("link",href=True):
            rel={str(x).lower() for x in (tag.get("rel") or [])}; asv=str(tag.get("as") or "").lower(); typ=str(tag.get("type") or "").lower()
            if "stylesheet" in rel or ("preload" in rel and asv=="style") or typ=="text/css":
                self.fetch_css(normalize_url(urljoin(page_url,tag["href"]),keep_query=True))
        for idx,style in enumerate(soup.find_all("style"),1):
            css=style.get_text("\n",strip=False)
            if not css.strip(): continue
            p=urlparse(page_url); key=hashlib.sha1(page_url.encode()).hexdigest()[:12]; rel=Path("inline-css")/(p.hostname or "host")/f"{key}-{idx:03d}.css"
            data=css.encode("utf-8",errors="replace"); local=safe_write(self.out,rel,data)
            self.entries.append(Entry(page_url,page_url,200,"text/css","inline-css",local,len(data),sha256(data),0,None))
            for imported in CSS_IMPORT_RE.findall(css): self.fetch_css(normalize_url(urljoin(page_url,imported),keep_query=True))

    def fetch_css(self,css_url):
        css_url=normalize_url(css_url,keep_query=True)
        if css_url in self.seen_css or urlparse(css_url).scheme not in {"http","https"}: return
        self.seen_css.add(css_url); host=urlparse(css_url).hostname or ""
        if host and host!=self.main_origin[1]: self.external_css_hosts.add(host)
        r=self.get(css_url)
        if r is None: return
        if r.status_code>=400:
            self.entries.append(Entry(css_url,r.url,r.status_code,content_type(r),"css-error",None,len(r.content),None,getattr(r,"_archive_elapsed_ms",None),None)); return
        self.save_response(css_url,r,"css",".css")
        try:
            for imported in CSS_IMPORT_RE.findall(r.text): self.fetch_css(normalize_url(urljoin(r.url,imported),keep_query=True))
        except Exception: pass

    def seed(self):
        self.enqueue_page(self.site)
        for sm in discover_sitemaps(self.session,self.site,self.timeout):
            for u in parse_sitemap(self.session,sm,self.timeout): self.enqueue_page(u)

    def run(self):
        self.out.mkdir(parents=True,exist_ok=True); started=now_iso(); self.seed(); pages_count=0
        while self.queue and pages_count<self.max_pages:
            url=self.queue.popleft()
            if url in self.seen_pages: continue
            self.seen_pages.add(url)
            if not self.allowed(url):
                self.entries.append(Entry(url,url,None,"","robots-skip",None,0,None,None,"Disallowed by robots.txt")); continue
            r=self.get(url)
            if r is None: continue
            ct=content_type(r)
            if r.status_code>=400:
                self.entries.append(Entry(url,r.url,r.status_code,ct,"html-error",None,len(r.content),None,getattr(r,"_archive_elapsed_ms",None),None)); continue
            if ct not in HTML_TYPES and not (not ct and b"<html" in r.content[:4096].lower()): continue
            self.save_response(url,r,"html",".html"); pages_count+=1; self.discover_html(r.url,r.content); print(f"[{pages_count:04d}] {r.status_code} {r.url}")
        summary={"site":self.site,"started_at":started,"finished_at":now_iso(),"pages_saved":sum(1 for e in self.entries if e.kind=="html" and e.local_path),"css_saved":sum(1 for e in self.entries if e.kind=="css" and e.local_path),"inline_css_saved":sum(1 for e in self.entries if e.kind=="inline-css"),"entries":len(self.entries),"external_css_hosts":sorted(self.external_css_hosts),"obey_robots":self.obey_robots,"max_pages":self.max_pages,"user_agent":UA}
        (self.out/"manifest.json").write_text(json.dumps({"summary":summary,"resources":[asdict(e) for e in self.entries]},ensure_ascii=False,indent=2),encoding="utf-8")
        (self.out/"SUMMARY.txt").write_text("\n".join(f"{k}: {v}" for k,v in summary.items()),encoding="utf-8")
        print(json.dumps(summary,ensure_ascii=False,indent=2))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--site",required=True); ap.add_argument("--out",required=True,type=Path); ap.add_argument("--delay",type=float,default=0.35); ap.add_argument("--timeout",type=int,default=25); ap.add_argument("--max-pages",type=int,default=500); ap.add_argument("--ignore-robots",action="store_true"); ap.add_argument("--keep-query",action="store_true"); a=ap.parse_args()
    Archiver(a.site,a.out,a.delay,a.timeout,a.max_pages,not a.ignore_robots,a.keep_query).run()
if __name__=="__main__": main()

# Triggered via ChatGPT on 2026-10-03
