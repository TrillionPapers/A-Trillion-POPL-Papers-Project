#!/usr/bin/env python3
"""Build the web site of the project.

Usage: python site/build.py OUTPUT_DIR

The site lists the ideas in ideas/ and the papers in papers/, shows the record and the PDF of
each paper, and renders RATIONALE.md and CONTRIBUTING.md. The script only reads files. It never
runs anything that a contribution contains, and HTML that comes from Markdown passes through an
allowlist.
"""

import html
import os
import posixpath
import re
import shutil
import sys
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote

import markdown
import yaml

ROOT = Path(__file__).resolve().parent.parent
REPO = os.environ.get("GITHUB_REPOSITORY", "TrillionPapers/A-Trillion-POPL-Papers-Project")
REPO_URL = f"https://github.com/{REPO}"
COMMIT = os.environ.get("GITHUB_SHA", "")
SITE_NAME = "A Trillion POPL Papers"
SLUG = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")
SCHEME = re.compile(r"^([a-zA-Z][a-zA-Z0-9+.\-]*):")
DOC_PAGES = {
    "README.md": "index.html",
    "RATIONALE.md": "rationale.html",
    "CONTRIBUTING.md": "contributing.html",
}

esc = html.escape


def read(path):
    return path.read_text(encoding="utf-8", errors="replace")


def warn(message):
    print(f"warning: {message}", file=sys.stderr)


# ---------------------------------------------------------------------------------------------
# Markdown, through an allowlist

ALLOWED_TAGS = {
    "p", "h1", "h2", "h3", "h4", "h5", "h6", "ul", "ol", "li", "a", "em", "strong", "code", "pre",
    "blockquote", "table", "thead", "tbody", "tr", "th", "td", "hr", "br", "sup", "sub", "del",
}
VOID_TAGS = {"br", "hr"}
DROPPED_WITH_CONTENT = {
    "script", "style", "iframe", "object", "embed", "template", "svg", "math", "noscript",
    "textarea", "title", "head", "form", "select", "button",
}


class Sanitizer(HTMLParser):
    """Rebuilds HTML from allowed tags only. The only attribute that survives is a checked href."""

    def __init__(self, link):
        super().__init__(convert_charrefs=True)
        self.link = link
        self.out = []
        self.dropping = 0

    def handle_starttag(self, tag, attrs):
        if tag in DROPPED_WITH_CONTENT:
            self.dropping += 1
            return
        if self.dropping or tag not in ALLOWED_TAGS:
            return
        attr = ""
        if tag == "a":
            href = self.link(dict(attrs).get("href") or "")
            if href:
                attr = f' href="{esc(href, quote=True)}"'
        self.out.append(f"<{tag}{attr}>")

    def handle_startendtag(self, tag, attrs):
        if tag not in DROPPED_WITH_CONTENT:
            self.handle_starttag(tag, attrs)
            if tag not in VOID_TAGS:
                self.handle_endtag(tag)

    def handle_endtag(self, tag):
        if tag in DROPPED_WITH_CONTENT:
            self.dropping = max(0, self.dropping - 1)
            return
        if not self.dropping and tag in ALLOWED_TAGS and tag not in VOID_TAGS:
            self.out.append(f"</{tag}>")

    def handle_data(self, data):
        if not self.dropping:
            self.out.append(esc(data, quote=False))


def linker(src_dir, base):
    """Maps the links of a Markdown file in the repository directory `src_dir` to links that
    work on a page whose path to the site root is `base`. Unsafe links map to the empty string."""

    def link(href):
        href = re.sub(r"[\x00-\x20\x7f]", "", href)
        if not href:
            return ""
        scheme = SCHEME.match(href)
        if scheme:
            return href if scheme.group(1).lower() in ("http", "https", "mailto") else ""
        if href.startswith("#") or href.startswith("//"):
            return href
        path, sep, fragment = href.partition("#")
        target = posixpath.normpath(posixpath.join(src_dir, path))
        if target.startswith(".."):
            return ""
        if target in DOC_PAGES:
            out = base + DOC_PAGES[target]
        elif re.fullmatch(r"ideas/[^/]+\.md", target):
            out = base + quote(target[:-3]) + ".html"
        else:
            kind = "tree" if (ROOT / target).is_dir() else "blob"
            out = f"{REPO_URL}/{kind}/main/{quote(target)}"
        return out + sep + quote(fragment)

    return link


def render_markdown(text, link):
    raw = markdown.markdown(text, extensions=["tables", "fenced_code"], output_format="html")
    sanitizer = Sanitizer(link)
    sanitizer.feed(raw)
    sanitizer.close()
    return "".join(sanitizer.out)


def plain(text):
    """Markdown source to one line of plain text, for summaries."""
    text = re.sub(r"`([^`]*)`", r"\1", text)
    text = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"[*_#>]", "", text)
    return " ".join(text.split())


def first_sentence(text, limit=260):
    """The first sentence of the first paragraph. A sentence of fewer than 40 characters is
    extended to the next sentence end, since a period that early is usually not an end."""
    for block in re.split(r"\n\s*\n", text):
        line = plain(block)
        if line:
            ends = [match.start() for match in re.finditer(r"(?<=[.?!])\s", line)]
            end = next((position for position in ends if position >= 40), len(line))
            sentence = line[:end]
            return sentence if len(sentence) <= limit else sentence[: limit - 1].rstrip() + "…"
    return ""


# ---------------------------------------------------------------------------------------------
# LaTeX, read for the abstract only

def detex(source):
    """A rough conversion of LaTeX prose to plain text."""
    s = re.sub(r"(?<!\\)%.*", "", source)
    s = s.replace("~", " ").replace("``", "\u201c").replace("''", "\u201d")
    s = s.replace("---", "\u2014").replace("--", "\u2013")
    for _ in range(4):
        s = re.sub(r"\\[a-zA-Z]+\*?(?:\[[^\]]*\])?\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\([%&_#$])", r"\1", s)
    s = re.sub(r"\\[a-zA-Z]+\s*", "", s)
    s = re.sub(r"[{}$\\]", "", s)
    return " ".join(s.split())


def abstract_of(tex):
    match = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", tex, flags=re.S)
    return detex(match.group(1)) if match else ""


# ---------------------------------------------------------------------------------------------
# Reading the repository

def text_of(value):
    return str(value).strip() if isinstance(value, (str, int, float)) else ""


def items_of(value):
    if value is None:
        return []
    return value if isinstance(value, list) else [value]


def load_ideas():
    ideas = []
    folder = ROOT / "ideas"
    for path in sorted(folder.glob("*.md")) if folder.is_dir() else []:
        if not SLUG.fullmatch(path.stem):
            warn(f"skipping {path.name}: unexpected file name")
            continue
        text = read(path)
        heading = re.search(r"^#\s+(.+?)\s*$", text, flags=re.M)
        title = plain(heading.group(1)) if heading else path.stem
        body = text[: heading.start()] + text[heading.end():] if heading else text
        ideas.append({
            "slug": path.stem, "title": title, "body": body, "summary": first_sentence(body),
        })
    return sorted(ideas, key=lambda idea: idea["title"].lower())


def load_papers():
    papers = []
    folder = ROOT / "papers"
    for path in sorted(folder.iterdir()) if folder.is_dir() else []:
        if not path.is_dir():
            continue
        if not SLUG.fullmatch(path.name):
            warn(f"skipping papers/{path.name}: unexpected directory name")
            continue
        meta, problem = {}, ""
        record = path / "meta.yaml"
        if record.is_file():
            try:
                loaded = yaml.safe_load(read(record))
                if isinstance(loaded, dict):
                    meta = loaded
                else:
                    problem = "meta.yaml is not a mapping."
            except yaml.YAMLError:
                problem = "meta.yaml could not be read."
        else:
            problem = "meta.yaml is missing."
        if problem:
            warn(f"papers/{path.name}: {problem}")
        tex = read(path / "paper.tex") if (path / "paper.tex").is_file() else ""
        abstract = abstract_of(tex)
        agents = []
        for agent in items_of(meta.get("agents")):
            if isinstance(agent, dict):
                agents.append({key: text_of(agent.get(key)) for key in ("model", "harness", "did")})
            elif text_of(agent):
                agents.append({"model": text_of(agent), "harness": "", "did": ""})
        humans = []
        for human in items_of(meta.get("humans")):
            if isinstance(human, dict):
                humans.append({key: text_of(human.get(key)) for key in ("name", "did")})
            elif text_of(human):
                humans.append({"name": text_of(human), "did": ""})
        verified = []
        for claim in items_of(meta.get("verified")):
            if isinstance(claim, dict):
                verified.append({key: text_of(claim.get(key)) for key in ("what", "by")})
        reviews = []
        review_folder = ROOT / "reviews" / path.name
        for review in sorted(review_folder.glob("*.md")) if review_folder.is_dir() else []:
            reviews.append({"name": review.stem, "body": read(review)})
        papers.append({
            "slug": path.name,
            "title": text_of(meta.get("title")) or path.name,
            "idea": text_of(meta.get("idea")),
            "builds_on": [text_of(name) for name in items_of(meta.get("builds-on")) if text_of(name)],
            "agents": [agent for agent in agents if agent["model"]],
            "humans": [human for human in humans if human["name"]],
            "verified": [claim for claim in verified if claim["what"]],
            "abstract": abstract,
            "summary": first_sentence(abstract),
            "problem": problem,
            "reviews": reviews,
            "pdf": (path / "paper.pdf").is_file(),
            "tex": bool(tex),
            "artifact": (path / "artifact").is_dir(),
        })
    return sorted(papers, key=lambda paper: paper["title"].lower())


# ---------------------------------------------------------------------------------------------
# Pages

def page(title, body, base):
    full_title = SITE_NAME if title == SITE_NAME else f"{title} · {SITE_NAME}"
    built = ""
    if COMMIT:
        built = (f' Built from commit <a href="{REPO_URL}/commit/{esc(COMMIT)}">'
                 f"{esc(COMMIT[:7])}</a>.")
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(full_title)}</title>
<link rel="stylesheet" href="{base}style.css">
</head>
<body>
<header><nav>
<a class="brand" href="{base}index.html">{esc(SITE_NAME)}</a>
<a href="{base}papers/index.html">Papers</a>
<a href="{base}ideas/index.html">Ideas</a>
<a href="{base}rationale.html">Rationale</a>
<a href="{base}contributing.html">Contributing</a>
<a href="{REPO_URL}">GitHub</a>
</nav></header>
<main>
{body}
</main>
<footer>Everything here comes from <a href="{REPO_URL}">the repository</a>.{built}</footer>
</body>
</html>
"""


def byline(paper):
    """The models that wrote the paper. A paper without an agent is credited to its humans."""
    names = [agent["model"] for agent in paper["agents"]] or [human["name"] for human in paper["humans"]]
    return ", ".join(esc(name) for name in names)


def paper_entry(paper, base):
    count = len(paper["verified"])
    claims = f"{count} verified claim{'s' if count != 1 else ''}"
    details = " · ".join(part for part in (byline(paper), claims) if part)
    summary = f"<p>{esc(paper['summary'])}</p>" if paper["summary"] else ""
    return (f'<li><a class="title" href="{base}papers/{quote(paper["slug"])}/index.html">'
            f'{esc(paper["title"])}</a>{summary}<p class="meta">{details}</p></li>')


def idea_entry(idea, base, papers):
    grown = [paper for paper in papers if paper["idea"] == idea["slug"]]
    note = ""
    if grown:
        links = ", ".join(
            f'<a href="{base}papers/{quote(paper["slug"])}/index.html">{esc(paper["title"])}</a>'
            for paper in grown)
        note = f'<p class="meta">Realized by {links}</p>'
    summary = f"<p>{esc(idea['summary'])}</p>" if idea["summary"] else ""
    return (f'<li><a class="title" href="{base}ideas/{quote(idea["slug"])}.html">'
            f'{esc(idea["title"])}</a>{summary}{note}</li>')


def entries(items):
    return '<ul class="entries">\n' + "\n".join(items) + "\n</ul>" if items else "<p>None yet.</p>"


def home_page(ideas, papers):
    readme = read(ROOT / "README.md") if (ROOT / "README.md").is_file() else ""
    heading = re.search(r"^#\s+(.+?)\s*$", readme, flags=re.M)
    name = plain(heading.group(1)) if heading else SITE_NAME
    lead = first_sentence(readme[heading.end():] if heading else readme, limit=400)
    body = f"""<h1>{esc(name)}</h1>
<p class="lead">{esc(lead)}</p>
<p class="actions"><a href="rationale.html">Why the project exists</a>
<a href="contributing.html">How to take part</a></p>
<h2>Papers <span class="count">{len(papers)}</span></h2>
{entries([paper_entry(paper, "") for paper in papers])}
<h2>Ideas <span class="count">{len(ideas)}</span></h2>
{entries([idea_entry(idea, "", papers) for idea in ideas])}"""
    return page(SITE_NAME, body, "")


def idea_page(idea, papers):
    base = "../"
    grown = [paper_entry(paper, base) for paper in papers if paper["idea"] == idea["slug"]]
    papers_html = f"<h2>Papers from this idea</h2>\n{entries(grown)}" if grown else ""
    source = f"{REPO_URL}/blob/main/ideas/{quote(idea['slug'])}.md"
    body = f"""<p class="kicker">Idea</p>
<h1>{esc(idea["title"])}</h1>
{render_markdown(idea["body"], linker("ideas", base))}
{papers_html}
<p class="meta"><a href="{source}">Source of this idea</a></p>"""
    return page(idea["title"], body, base)


def record_rows(paper, ideas, papers, base):
    rows = []
    known_ideas = {idea["slug"]: idea for idea in ideas}
    known_papers = {other["slug"]: other for other in papers}
    if paper["idea"]:
        idea = known_ideas.get(paper["idea"])
        value = (f'<a href="{base}ideas/{quote(idea["slug"])}.html">{esc(idea["title"])}</a>'
                 if idea else esc(paper["idea"]))
        rows.append(("Idea", value))
    if paper["builds_on"]:
        links = []
        for name in paper["builds_on"]:
            other = known_papers.get(name)
            links.append(
                f'<a href="{base}papers/{quote(other["slug"])}/index.html">{esc(other["title"])}</a>'
                if other else esc(name))
        rows.append(("Builds on", ", ".join(links)))
    for agent in paper["agents"]:
        value = esc(agent["model"])
        if agent["harness"]:
            value += f" in {esc(agent['harness'])}"
        if agent["did"]:
            value += f": {esc(agent['did'])}"
        rows.append(("Agent", value))
    for human in paper["humans"]:
        value = esc(human["name"])
        if human["did"]:
            value += f": {esc(human['did'])}"
        rows.append(("Human", value))
    return "\n".join(f"<dt>{label}</dt><dd>{value}</dd>" for label, value in rows)


def paper_page(paper, ideas, papers):
    base = "../../"
    folder = f"papers/{quote(paper['slug'])}"
    actions = []
    if paper["pdf"]:
        actions.append('<a class="button" href="paper.pdf">Read the PDF</a>')
    if paper["tex"]:
        actions.append(f'<a href="{REPO_URL}/blob/main/{folder}/paper.tex">LaTeX source</a>')
    if paper["artifact"]:
        actions.append(f'<a href="{REPO_URL}/tree/main/{folder}/artifact">Artifact</a>')
    actions.append(f'<a href="{REPO_URL}/tree/main/{folder}">All files</a>')
    parts = [
        '<p class="kicker">Paper</p>',
        f"<h1>{esc(paper['title'])}</h1>",
        f'<p class="byline">{byline(paper)}</p>' if byline(paper) else "",
        f'<p class="actions">{" ".join(actions)}</p>',
    ]
    if paper["problem"]:
        parts.append(f'<p class="meta">The record of this paper is incomplete: {esc(paper["problem"])}</p>')
    if paper["abstract"]:
        parts.append(f"<h2>Abstract</h2>\n<p>{esc(paper['abstract'])}</p>")
    rows = record_rows(paper, ideas, papers, base)
    if rows:
        parts.append(f'<h2>Record</h2>\n<dl class="record">\n{rows}\n</dl>')
    parts.append("<h2>Verified</h2>")
    if paper["verified"]:
        claims = "\n".join(
            f"<tr><td>{esc(claim['what'])}</td><td><code>{esc(claim['by'])}</code></td></tr>"
            for claim in paper["verified"])
        parts.append("<p>A command in the paper's directory checks each of these claims. "
                     "Every other claim of the paper is unverified.</p>\n"
                     f"<table><thead><tr><th>Claim</th><th>Checked by</th></tr></thead>\n"
                     f"<tbody>\n{claims}\n</tbody></table>")
    else:
        parts.append("<p>No claim of this paper is checked by a command.</p>")
    if paper["reviews"]:
        parts.append("<h2>Reviews</h2>")
        for review in paper["reviews"]:
            parts.append(f"<h3>{esc(review['name'])}</h3>\n"
                         + render_markdown(review["body"], linker(f"reviews/{paper['slug']}", base)))
    if paper["pdf"]:
        parts.append('<h2>PDF</h2>\n<object class="pdf" data="paper.pdf" type="application/pdf">'
                     '<p>This browser does not show PDFs inline. '
                     '<a href="paper.pdf">Open the PDF</a>.</p></object>')
    return page(paper["title"], "\n".join(part for part in parts if part), base)


def doc_page(name, title):
    path = ROOT / name
    text = read(path) if path.is_file() else f"# {title}\n\nThis file is missing."
    return page(title, render_markdown(text, linker("", "")), "")


def build(out):
    if out.exists():
        shutil.rmtree(out)
    (out / "ideas").mkdir(parents=True)
    (out / "papers").mkdir()
    ideas, papers = load_ideas(), load_papers()

    def write(relative, content):
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8")

    shutil.copyfile(ROOT / "site" / "style.css", out / "style.css")
    write("index.html", home_page(ideas, papers))
    write("rationale.html", doc_page("RATIONALE.md", "Rationale"))
    write("contributing.html", doc_page("CONTRIBUTING.md", "Contributing"))
    write("ideas/index.html", page("Ideas", f"""<h1>Ideas <span class="count">{len(ideas)}</span></h1>
<p>An idea is a few sentences. Agents and humans pick ideas up and write them into papers.</p>
{entries([idea_entry(idea, "../", papers) for idea in ideas])}""", "../"))
    for idea in ideas:
        write(f"ideas/{idea['slug']}.html", idea_page(idea, papers))
    write("papers/index.html", page("Papers", f"""<h1>Papers <span class="count">{len(papers)}</span></h1>
<p>Each paper records who wrote it and which of its claims a command checks.</p>
{entries([paper_entry(paper, "../") for paper in papers])}""", "../"))
    for paper in papers:
        write(f"papers/{paper['slug']}/index.html", paper_page(paper, ideas, papers))
        if paper["pdf"]:
            shutil.copyfile(ROOT / "papers" / paper["slug"] / "paper.pdf",
                            out / "papers" / paper["slug"] / "paper.pdf")
    print(f"built {len(ideas)} ideas and {len(papers)} papers into {out}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    build(Path(sys.argv[1]).resolve())
