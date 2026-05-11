#!/usr/bin/env python3
"""
Generate a static academic website from a LaTeX CV + BibTeX files.

Usage:
    python generate.py /path/to/cv-redux/
    python generate.py /path/to/cv-redux/ --output ./output
"""

import argparse
import gzip
import io
import json
import re
import shutil
import subprocess
import tarfile
import tempfile
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from difflib import SequenceMatcher
from pathlib import Path

import bibtexparser
from bibtexparser.bparser import BibTexParser
from jinja2 import Environment, FileSystemLoader

SELF_DIR = Path(__file__).parent
TEMPLATES_DIR = SELF_DIR / "templates"
STATIC_DIR = SELF_DIR / "static"

ARXIV_CACHE = SELF_DIR / "arxiv_cache.json"


MY_NAME_VARIANTS = [
    "Byron C. Wallace",
    "Byron C Wallace",
    "Wallace, Byron C.",
    "Wallace, Byron C",
    "Byron Wallace",
]

BIB_FILES = {
    "conference":   ("conference_papers.bib",  "Conference Papers"),
    "journal":      ("journal_papers.bib",      "Journal Articles"),
    "workshop":     ("workshop_papers.bib",      "Workshop & Symposium Papers"),
    "book_chapter": ("book_chapters.bib",        "Book Chapters"),
    "commentary":   ("commentaries.bib",         "Commentaries & Editorials"),
}


# ── BibTeX helpers ────────────────────────────────────────────────────────────

def load_bib(path):
    if not path.exists():
        print(f"  [skip] {path.name} not found")
        return []
    parser = BibTexParser(common_strings=True)
    parser.ignore_nonstandard_types = False
    try:
        bib = bibtexparser.loads(path.read_text(encoding="utf-8", errors="replace"), parser)
        return bib.entries
    except Exception as e:
        print(f"  [warn] {path.name}: {e}")
        return []


_DROP_CMDS = re.compile(
    r"\\(?:vspace|hspace|kern|mbox|phantom|rule|raisebox|smash)"
    r"\*?(?:\[[^\]]*\])?\{[^{}]*\}"
)

def clean_latex(text):
    if not text:
        return ""
    # Strip LaTeX comments
    text = re.sub(r"%[^\n]*", "", text)
    # Drop layout/spacing commands and their arguments entirely
    text = _DROP_CMDS.sub("", text)
    # Formatting commands: keep the inner text
    for cmd in ("textbf", "textit", "emph", "text", "bf", "it", "large",
                "small", "footnotesize", "tiny", "normalsize"):
        text = re.sub(rf"\\{cmd}\{{([^{{}}]*)\}}", r"\1", text)
    text = re.sub(r"\\href\{[^}]*\}\{([^}]*)\}", r"\1", text)
    text = re.sub(r"\\url\{[^}]*\}", "", text)
    # Any remaining single-arg command: keep the argument
    text = re.sub(r"\\[a-zA-Z]+\{([^{}]*)\}", r"\1", text)
    # Bare commands with no argument
    text = re.sub(r"\\[a-zA-Z@]+\*?", "", text)
    text = text.replace("{", "").replace("}", "")
    text = text.replace("~", " ")
    text = text.replace("---", "—").replace("--", "–")
    text = text.replace("``", """).replace("''", """)
    return re.sub(r"\s+", " ", text).strip()


def bold_my_name(s):
    for variant in MY_NAME_VARIANTS:
        if variant in s:
            return s.replace(variant, f"<strong>{variant}</strong>", 1)
    return s


def fmt_authors(raw):
    parts = re.split(r"\s+and\s+", raw, flags=re.IGNORECASE)
    people = []
    for part in parts:
        part = part.strip()
        if "," in part and not re.search(r"\d", part):
            last, first = part.split(",", 1)
            part = f"{first.strip()} {last.strip()}"
        people.append(part)
    return bold_my_name(", ".join(people))


def _arxiv_url_from_entry(e):
    url = e.get("url") or ""
    if "arxiv.org" in url:
        return url
    eprint = e.get("eprint", "").strip()
    prefix = e.get("archiveprefix", "").strip().lower()
    if eprint and prefix == "arxiv":
        return f"https://arxiv.org/abs/{eprint}"
    return url


def entry_to_pub(e, kind):
    year_str = e.get("year", "0")
    try:
        year_int = int(re.sub(r"\D", "", year_str)[:4])
    except (ValueError, TypeError):
        year_int = 0

    venue = clean_latex(
        e.get("journal") or e.get("booktitle") or e.get("howpublished") or ""
    )
    return {
        "year": year_str,
        "year_int": year_int,
        "title": clean_latex(e.get("title", "")),
        "authors": fmt_authors(e.get("author", "")),
        "venue": venue,
        "volume": e.get("volume", ""),
        "number": e.get("number", ""),
        "pages": e.get("pages", ""),
        "note": clean_latex(e.get("note", "")),
        "url": _arxiv_url_from_entry(e),
        "kind": kind,
    }


def load_publications(cv_dir):
    pubs = {}
    for kind, (fname, label) in BIB_FILES.items():
        entries = load_bib(cv_dir / fname)
        pubs[kind] = {
            "label": label,
            "entries": sorted(
                [entry_to_pub(e, kind) for e in entries if e.get("author") or e.get("title")],
                key=lambda x: x["year_int"],
                reverse=True,
            ),
        }
        print(f"  {kind}: {len(pubs[kind]['entries'])} entries")
    return pubs


# ── LaTeX parsing helpers ─────────────────────────────────────────────────────

def extract_brace(text, start):
    """Extract content of balanced {} at position `start` (which must be '{')."""
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1: i], i + 1
    return text[start + 1:], len(text)


def parse_cvlines(tex):
    """Return [{label, value}] for every \\cvline{label}{value} in tex."""
    results = []
    i = 0
    while True:
        m = re.search(r"\\cvline", tex[i:])
        if not m:
            break
        pos = i + m.end()
        while pos < len(tex) and tex[pos] in " \t":
            pos += 1
        if pos >= len(tex) or tex[pos] != "{":
            i = pos
            continue
        label, pos = extract_brace(tex, pos)
        while pos < len(tex) and tex[pos] in " \t":
            pos += 1
        if pos >= len(tex) or tex[pos] != "{":
            i = pos
            continue
        value, pos = extract_brace(tex, pos)
        results.append({"label": label.strip(), "value": value.strip()})
        i = pos
    return results


def section_text(tex, header_pattern):
    """Return the body of the first \\section matching header_pattern."""
    m = re.search(rf"\\section\{{{header_pattern}[^}}]*\}}", tex)
    if not m:
        return ""
    rest = tex[m.end():]
    nxt = re.search(r"\\section\{", rest)
    return rest[: nxt.start()] if nxt else rest


# ── CV section parsers ────────────────────────────────────────────────────────

def parse_grants(tex):
    sec = section_text(tex, r"Research Support")
    cvlines = parse_cvlines(sec)
    grants, current = [], None
    for cl in cvlines:
        label = cl["label"]
        value = cl["value"]
        if label == "Grant Title":
            if current:
                grants.append(current)
            current = {
                "title": clean_latex(value),
                "funder": "", "role": "", "period": "",
                "amount": "", "collaborators": "", "pi": "",
            }
        elif current is not None:
            lk = label.lower()
            if lk == "funder":
                current["funder"] = clean_latex(value)
            elif lk == "role":
                current["role"] = clean_latex(value)
            elif lk == "period":
                current["period"] = clean_latex(value)
            elif lk == "amount":
                current["amount"] = clean_latex(value)
            elif lk == "collaborators":
                current["collaborators"] = clean_latex(value)
            elif lk == "pi":
                current["pi"] = clean_latex(value)
    if current:
        grants.append(current)
    return grants


def parse_honors(tex):
    sec = section_text(tex, r"Academic honors")
    honors = []
    for cl in parse_cvlines(sec):
        if re.match(r"^\d{4}$", cl["label"]):
            honors.append({"year": cl["label"], "text": clean_latex(cl["value"])})
    return honors


def parse_research_interests(tex):
    sec = section_text(tex, r"Research interests")
    for cl in parse_cvlines(sec):
        if cl["label"] == "":
            return clean_latex(cl["value"])
    return ""


def parse_bio(tex):
    fn_m = re.search(r"\\firstname\{([^}]+)\}", tex)
    ln_m = re.search(r"\\familyname\{([^}]+)\}", tex)
    name = f"{fn_m.group(1)} {ln_m.group(1)}" if fn_m and ln_m else ""

    title_m = re.search(
        r"\\begin\{document\}.*?\\maketitle[^\n]*\n(.*?)(?=\\section)",
        tex, re.DOTALL
    )
    title_line = ""
    if title_m:
        raw = title_m.group(1)
        # Strip comment lines before cleaning
        raw = re.sub(r"^\s*%.*$", "", raw, flags=re.MULTILINE)
        title_line = clean_latex(raw)

    return {"name": name, "title_line": title_line, "email": "b.wallace@northeastern.edu"}


def parse_current_students(tex):
    sec = section_text(tex, r"Advising")
    m = re.search(r"\\underline\{Current Northeastern CS PhD students\}", sec)
    if not m:
        return []
    rest = sec[m.end():]
    stop = re.search(r"\\underline", rest)
    chunk = rest[: stop.start()] if stop else rest
    students = []
    for cl in parse_cvlines(chunk):
        if cl["label"] and cl["value"]:
            students.append({
                "period": clean_latex(cl["label"]),
                "info": clean_latex(cl["value"]),
            })
    return students


def parse_dissertations(tex):
    sec = section_text(tex, r"Advising")
    m = re.search(r"\\underline\{Ph\.D\. Dissertations Supervised\}", sec)
    if not m:
        return []
    rest = sec[m.end():]
    stop = re.search(r"\\subsection", rest)
    chunk = rest[: stop.start()] if stop else rest

    dissertations, current = [], None
    for cl in parse_cvlines(chunk):
        label = cl["label"]
        value = clean_latex(cl["value"])
        year_m = re.search(r"\d{4}", label)
        if year_m and re.match(r"^[\d/]+$", label.strip()):
            if current:
                dissertations.append(current)
            year = year_m.group(0)
            current = {"year": year, "name": value, "thesis_title": "", "now_at": ""}
        elif current is not None and label == "":
            if value.startswith("Thesis title:"):
                current["thesis_title"] = value.replace("Thesis title:", "").strip().strip(".")
            elif "Now at" in value:
                current["now_at"] = re.sub(r".*?Now at\s*:?\s*", "", value).strip()
    if current:
        dissertations.append(current)
    return sorted(dissertations, key=lambda x: x["year"], reverse=True)


# ── arXiv enrichment ─────────────────────────────────────────────────────────

def _norm(title):
    t = title.lower()
    t = re.sub(r"[^\w\s]", " ", t)
    return re.sub(r"\s+", " ", t).strip()


def _load_arxiv_cache():
    if ARXIV_CACHE.exists():
        return json.loads(ARXIV_CACHE.read_text(encoding="utf-8"))
    return {}


def _save_arxiv_cache(cache):
    ARXIV_CACHE.write_text(json.dumps(cache, indent=2, sort_keys=True), encoding="utf-8")


_ARXIV_NS = "http://www.w3.org/2005/Atom"


def _arxiv_lookup(title, cache):
    """Query the arXiv API by title. Returns arXiv URL string or None."""
    key = _norm(title)
    if key in cache and cache[key]:
        return cache[key]
    if key in cache and cache[key] is None:
        return None  # previously confirmed not on arXiv

    query = urllib.parse.quote(f'ti:"{title}"')
    url = f"http://export.arxiv.org/api/query?search_query={query}&max_results=5&sortBy=relevance"
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "bcw-academic-site/1.0"})
        with urllib.request.urlopen(req, timeout=15) as r:
            xml_data = r.read()
        time.sleep(3.0)  # arXiv API: max 1 req/3 sec
        root = ET.fromstring(xml_data)
        for entry in root.findall(f"{{{_ARXIV_NS}}}entry"):
            arxiv_title = entry.findtext(f"{{{_ARXIV_NS}}}title", "").replace("\n", " ").strip()
            ratio = SequenceMatcher(None, key, _norm(arxiv_title)).ratio()
            if ratio >= 0.85:
                arxiv_id_url = entry.findtext(f"{{{_ARXIV_NS}}}id", "").strip()
                arxiv_id_url = re.sub(r"v\d+$", "", arxiv_id_url)
                cache[key] = arxiv_id_url
                return arxiv_id_url
        cache[key] = None
        return None
    except urllib.error.HTTPError as e:
        if e.code == 429:
            print(f"  [rate limit] pausing 60s...")
            time.sleep(60)
        else:
            print(f"  [warn] arXiv error for '{title[:50]}': {e}")
            cache[key] = None
        return None  # don't cache 429 failures — they'll retry next run
    except Exception as e:
        print(f"  [warn] arXiv lookup failed for '{title[:50]}': {e}")
        return None


def enrich_arxiv(pubs, fetch=False):
    """Add arXiv URLs to pubs. Uses cache; queries S2 when fetch=True."""
    cache = _load_arxiv_cache()
    all_entries = [e for g in pubs.values() for e in g["entries"]]
    to_fetch = []

    for pub in all_entries:
        if pub["url"] and "arxiv.org" in pub["url"]:
            continue
        key = _norm(pub["title"])
        if key in cache and cache[key]:
            pub["url"] = cache[key]
        elif fetch:
            to_fetch.append(pub)  # includes uncached AND previously-null entries

    if to_fetch:
        est = len(to_fetch) // 2
        print(f"  Querying arXiv for {len(to_fetch)} papers (~{est}s)...")
        found = 0
        for i, pub in enumerate(to_fetch):
            result = _arxiv_lookup(pub["title"], cache)
            if result:
                pub["url"] = result
                found += 1
            if (i + 1) % 20 == 0:
                _save_arxiv_cache(cache)
                print(f"  {i + 1}/{len(to_fetch)} checked, {found} found so far")
        _save_arxiv_cache(cache)
        print(f"  Done: {found}/{len(to_fetch)} arXiv links found and cached.")


# ── Paper figures ────────────────────────────────────────────────────────────

FIGURES_CACHE = SELF_DIR / "figures_cache.json"


def _load_figures_cache():
    if FIGURES_CACHE.exists():
        return json.loads(FIGURES_CACHE.read_text(encoding="utf-8"))
    return {}


def _save_figures_cache(cache):
    FIGURES_CACHE.write_text(json.dumps(cache, indent=2, sort_keys=True), encoding="utf-8")


def _arxiv_id_from_url(url):
    m = re.search(r"arxiv\.org/(?:abs|pdf)/([0-9]{4}\.[0-9v]+)", url)
    return re.sub(r"v\d+$", "", m.group(1)) if m else None


def _convert_pdf_to_png(pdf_data, output_path):
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        pdf = tmp / "fig.pdf"
        pdf.write_bytes(pdf_data)
        r = subprocess.run(
            ["pdftoppm", "-r", "150", "-f", "1", "-l", "1", "-png",
             str(pdf), str(tmp / "out")],
            capture_output=True, timeout=30,
        )
        hits = sorted(tmp.glob("out*.png"))
        if hits:
            output_path.write_bytes(hits[0].read_bytes())
            return True
    return False


def _convert_eps_to_png(eps_data, output_path):
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        eps = tmp / "fig.eps"
        eps.write_bytes(eps_data)
        r = subprocess.run(
            ["gs", "-dNOPAUSE", "-dBATCH", "-sDEVICE=png16m", "-r150",
             f"-sOutputFile={output_path}", str(eps)],
            capture_output=True, timeout=30,
        )
        return output_path.exists()


def _extract_first_figure(tar):
    """Parse .tex to find first \\includegraphics, extract and return (data, ext)."""
    # Find main tex file
    tex_files = sorted(
        [m for m in tar.getmembers() if m.isfile() and m.name.endswith(".tex")],
        key=lambda m: len(m.name),
    )
    main_tex = ""
    for tf in tex_files:
        try:
            content = tar.extractfile(tf).read().decode("utf-8", errors="replace")
            if r"\documentclass" in content or r"\begin{document}" in content:
                main_tex = content
                break
        except Exception:
            continue
    if not main_tex and tex_files:
        try:
            main_tex = tar.extractfile(tex_files[0]).read().decode("utf-8", errors="replace")
        except Exception:
            pass
    if not main_tex:
        return None, None

    # Build member lookup by stem and basename
    member_map = {}
    for m in tar.getmembers():
        if not m.isfile():
            continue
        p = Path(m.name)
        for key in (m.name.lower(), p.name.lower(), p.stem.lower()):
            member_map.setdefault(key, m)

    refs = re.findall(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}", main_tex)
    for ref in refs[:10]:
        ref = ref.strip()
        stem = Path(ref).stem.lower()
        basename = Path(ref).name.lower()
        for key in (ref.lower(), basename, stem):
            m = member_map.get(key)
            if m:
                ext = Path(m.name).suffix.lower()
                if ext in (".pdf", ".eps", ".png", ".jpg", ".jpeg", ""):
                    try:
                        return tar.extractfile(m).read(), ext or ".pdf"
                    except Exception:
                        continue
        for ext in (".pdf", ".eps", ".png", ".jpg", ".jpeg"):
            m = member_map.get(stem + ext)
            if m:
                try:
                    return tar.extractfile(m).read(), ext
                except Exception:
                    continue
    return None, None


def fetch_paper_figure(arxiv_url, figures_dir):
    """Download arXiv source for one paper, extract Figure 1, save as PNG."""
    arxiv_id = _arxiv_id_from_url(arxiv_url)
    if not arxiv_id:
        return None
    safe_id = arxiv_id.replace("/", "_")
    out = figures_dir / f"{safe_id}.png"
    if out.exists():
        return out.name

    try:
        req = urllib.request.Request(
            f"https://arxiv.org/e-print/{arxiv_id}",
            headers={"User-Agent": "bcw-academic-site/1.0"},
        )
        with urllib.request.urlopen(req, timeout=30) as r:
            raw = r.read()
        time.sleep(5.0)
    except Exception as e:
        print(f"    [warn] download failed: {e}")
        return None

    # Decompress outer gzip envelope
    try:
        data = gzip.decompress(raw)
    except Exception:
        data = raw

    # Try as tarball (LaTeX source)
    try:
        with tarfile.open(fileobj=io.BytesIO(data)) as tar:
            fig_data, ext = _extract_first_figure(tar)
            if fig_data:
                if ext in (".png", ".jpg", ".jpeg"):
                    out.write_bytes(fig_data)
                    return out.name
                if ext in (".pdf", ""):
                    return out.name if _convert_pdf_to_png(fig_data, out) else None
                if ext == ".eps":
                    return out.name if _convert_eps_to_png(fig_data, out) else None
    except tarfile.TarError:
        # PDF-only submission — grab page 1
        if data[:4] == b"%PDF":
            return out.name if _convert_pdf_to_png(data, out) else None

    return None


def fetch_figures(pubs, n, static_dir):
    """Fetch Figure 1 for the N most recent arXiv papers. Returns list of dicts."""
    figures_dir = static_dir / "paper-figures"
    figures_dir.mkdir(exist_ok=True)
    cache = _load_figures_cache()

    candidates = sorted(
        [e for g in pubs.values() for e in g["entries"]
         if "arxiv.org" in (e.get("url") or "")],
        key=lambda x: x["year_int"], reverse=True,
    )[:n]

    print(f"  Fetching figures for up to {len(candidates)} papers...")
    results = []
    for pub in candidates:
        arxiv_id = _arxiv_id_from_url(pub["url"])
        if not arxiv_id:
            continue
        if arxiv_id in cache:
            fname = cache[arxiv_id]
        else:
            print(f"  [{arxiv_id}] {pub['title'][:55]}...")
            fname = fetch_paper_figure(pub["url"], figures_dir)
            cache[arxiv_id] = fname
            _save_figures_cache(cache)
            print(f"    -> {'ok: ' + fname if fname else 'not found'}")

        if fname and (figures_dir / fname).exists():
            results.append({
                "title": pub["title"],
                "year": pub["year"],
                "url": pub["url"],
                "figure": fname,
            })

    print(f"  Got {len(results)} figures.")
    return results


# ── students.txt loader ───────────────────────────────────────────────────────

def load_students_txt():
    """Read students.txt. Returns (current_students, alumni) or (None, None) if missing."""
    path = SELF_DIR / "students.txt"
    if not path.exists():
        return None, None
    text = path.read_text(encoding="utf-8")
    students = []
    current = None
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if stripped.startswith("[") and stripped.endswith("]"):
            if current:
                students.append(current)
            current = {"name": stripped[1:-1]}
        elif current is not None and ":" in stripped:
            key, _, val = stripped.partition(":")
            current[key.strip().lower()] = val.strip()
    if current:
        students.append(current)
    current_students = [s for s in students if s.get("status") == "current"]
    alumni = [s for s in students if s.get("status") == "alumni"]
    return current_students, alumni


# ── bio.txt override ─────────────────────────────────────────────────────────

_BIO_INLINE_KEYS = {"email", "scholar", "bluesky", "twitter"}
_BIO_BLOCK_KEYS  = {"title", "interests"}

def load_bio_override():
    """Read bio.txt. Returns dict with title, interests, email, scholar, bluesky, twitter."""
    path = SELF_DIR / "bio.txt"
    if not path.exists():
        return {}
    text = path.read_text(encoding="utf-8")
    result = {}
    current_key = None
    current_lines = []
    for line in text.splitlines():
        stripped = line.strip()
        # Inline single-value keys (key: value on one line)
        m = re.match(r"^(" + "|".join(_BIO_INLINE_KEYS) + r"):\s*(.+)$", stripped)
        if m:
            if current_key:
                result[current_key] = " ".join(current_lines).strip()
                current_key = None
                current_lines = []
            result[m.group(1)] = m.group(2).strip()
            continue
        # Block keys (key: on its own line, content follows)
        if stripped.rstrip(":") in _BIO_BLOCK_KEYS and stripped.endswith(":"):
            if current_key:
                result[current_key] = " ".join(current_lines).strip()
            current_key = stripped.rstrip(":")
            current_lines = []
        elif current_key and stripped:
            current_lines.append(stripped)
    if current_key:
        result[current_key] = " ".join(current_lines).strip()
    return result


# ── Site generation ───────────────────────────────────────────────────────────

def render(env, template_name, output_path, **ctx):
    html = env.get_template(template_name).render(**ctx)
    output_path.write_text(html, encoding="utf-8")
    print(f"  wrote {output_path}")


def generate(cv_dir, output_dir, fetch_arxiv=False):
    cv_dir = Path(cv_dir).resolve()
    output_dir = Path(output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    static_out = output_dir / "static"
    if static_out.exists():
        shutil.rmtree(static_out)
    shutil.copytree(STATIC_DIR, static_out)

    tex = (cv_dir / "bcw-cv.tex").read_text(encoding="utf-8", errors="replace")

    print("Parsing CV...")
    bio = parse_bio(tex)
    interests = parse_research_interests(tex)

    override = load_bio_override()
    if "title" in override:
        bio["title_line"] = override["title"]
        print(f"  title: overridden from bio.txt")
    if "interests" in override:
        interests = override["interests"]
        print(f"  interests: overridden from bio.txt")
    for key in ("email", "scholar", "bluesky", "twitter"):
        bio[key] = override.get(key, "")

    honors = parse_honors(tex)

    current_students, alumni = load_students_txt()
    if current_students is None:
        print("  [warn] students.txt not found, falling back to CV")
        cv_students = parse_current_students(tex)
        cv_diss = parse_dissertations(tex)
        current_students = [{"name": s["info"], "info": "", "image": "", "link": ""} for s in cv_students]
        alumni = [{"name": d["name"], "graduation": d["year"], "thesis": d["thesis_title"], "now": d["now_at"], "image": "", "link": ""} for d in cv_diss]

    print(f"  bio: {bio['name']}")
    print(f"  honors: {len(honors)}")
    print(f"  current students: {len(current_students)}")
    print(f"  alumni: {len(alumni)}")

    print("Loading publications...")
    pubs = load_publications(cv_dir)
    enrich_arxiv(pubs, fetch=fetch_arxiv)

    env = Environment(loader=FileSystemLoader(str(TEMPLATES_DIR)), autoescape=False)
    pub_kinds = list(BIB_FILES.keys())
    ctx = dict(bio=bio, pub_kinds=pub_kinds)

    # Collect the 6 most recent papers across conference + journal
    all_recent = sorted(
        pubs["conference"]["entries"] + pubs["journal"]["entries"],
        key=lambda x: x["year_int"],
        reverse=True,
    )[:6]

    # CNAME for GitHub Pages custom domain
    (output_dir / "CNAME").write_text("byronwallace.com\n", encoding="utf-8")

    print("Rendering pages...")
    render(env, "index.html", output_dir / "index.html",
           active="about", interests=interests, recent_papers=all_recent, **ctx)
    render(env, "publications.html", output_dir / "publications.html",
           active="publications", pubs=pubs, **ctx)
    render(env, "students.html", output_dir / "students.html",
           active="students", current_students=current_students, alumni=alumni, **ctx)
    render(env, "teaching.html", output_dir / "teaching.html",
           active="teaching", **ctx)
    print("Done.")


def main():
    parser = argparse.ArgumentParser(description="Generate academic website from CV.")
    parser.add_argument("cv_dir", help="Path to directory containing bcw-cv.tex and .bib files")
    parser.add_argument("--output", default="docs", help="Output directory (default: ./docs)")
    parser.add_argument("--fetch-arxiv", action="store_true",
                        help="Query arXiv for missing arXiv links and cache results")
    args = parser.parse_args()
    generate(args.cv_dir, args.output, fetch_arxiv=args.fetch_arxiv)


if __name__ == "__main__":
    main()
