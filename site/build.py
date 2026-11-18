#!/usr/bin/env python3
"""Build the web site of the project.

Usage: python site/build.py OUTPUT_DIR

The site lists the ideas in ideas/ and the papers in papers/ with their sequence numbers, shows
the record, the versions, the reviews, and the PDF of each paper, renders RATIONALE.md and
CONTRIBUTING.md, and writes a search page with its index, search.json. Earlier versions of a paper are read from the git history at the commits that
papers/VERSIONS records.

The script only reads files. It never runs anything that a contribution contains, and HTML that
comes from Markdown passes through an allowlist.
"""

import html
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote

import markdown
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ids  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
REPO = os.environ.get("GITHUB_REPOSITORY", "TrillionPapers/A-Trillion-POPL-Papers-Project")
REPO_URL = f"https://github.com/{REPO}"
OWNER, _, PROJECT = REPO.partition("/")
SITE_URL = os.environ.get("SITE_URL", f"https://{OWNER.lower()}.github.io/{PROJECT}/")
COMMIT = os.environ.get("GITHUB_SHA", "")
SITE_NAME = "A Trillion POPL Papers"
GOAL = 1_000_000_000_000
PREFIX = "tpp"
SLUG = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")
SCHEME = re.compile(r"^([a-zA-Z][a-zA-Z0-9+.\-]*):")
MACRO = re.compile(r"\\newcommand\{\\([A-Za-z]+)\}\{([^{}]*)\}")
INPUT = re.compile(r"\\input\{([^{}]+)\}")
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
# The files of a paper, in the working tree or at a commit

class Source:
    """Reads the files of one paper directory. With a commit, it reads that state from git."""

    def __init__(self, name, commit=None):
        self.name, self.commit = name, commit
        self.folder = ROOT / "papers" / name

    def _clean(self, relative):
        parts = relative.split("/")
        if relative.startswith("/") or any(part in ("", ".", "..") for part in parts):
            return None
        return relative

    def data(self, relative, limit=50_000_000):
        relative = self._clean(relative)
        if relative is None:
            return None
        if self.commit is None:
            path = self.folder / relative
            try:
                inside = self.folder.resolve() in path.resolve().parents
                if inside and path.is_file() and path.stat().st_size <= limit:
                    return path.read_bytes()
            except OSError:
                pass
            return None
        try:
            done = subprocess.run(
                ["git", "-C", str(ROOT), "show", f"{self.commit}:papers/{self.name}/{relative}"],
                capture_output=True, check=True)
        except (OSError, subprocess.CalledProcessError):
            return None
        return done.stdout if len(done.stdout) <= limit else None

    def text(self, relative):
        data = self.data(relative, limit=2_000_000)
        return data.decode("utf-8", errors="replace") if data is not None else None

    def has_directory(self, relative):
        if self.commit is None:
            return (self.folder / relative).is_dir()
        return ids.git("cat-file", "-t", f"{self.commit}:papers/{self.name}/{relative}") == "tree"


# ---------------------------------------------------------------------------------------------
# LaTeX, read for the abstract only

def macros_of(source, tex):
    """Macros without arguments that the paper defines, in its own file or in a file of its
    directory that it includes."""
    texts = [tex]
    for name in INPUT.findall(tex):
        included = source.text(name if name.endswith(".tex") else name + ".tex")
        if included is not None:
            texts.append(included)
    return {name: value for text in texts for name, value in MACRO.findall(text)}


def detex(source, macros):
    """A rough conversion of LaTeX prose to plain text."""
    s = re.sub(r"(?<!\\)%.*", "", source)
    s = re.sub(r"\\([A-Za-z]+)", lambda match: macros.get(match.group(1), match.group(0)), s)
    s = s.replace("~", " ").replace("``", "\u201c").replace("''", "\u201d")
    s = s.replace("---", "\u2014").replace("--", "\u2013")
    for _ in range(4):
        s = re.sub(r"\\[a-zA-Z]+\*?(?:\[[^\]]*\])?\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\([%&_#$])", r"\1", s)
    s = re.sub(r"\\[a-zA-Z]+\s*", "", s)
    s = re.sub(r"[{}$\\]", "", s)
    return " ".join(s.split())


def abstract_of(source, tex):
    match = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", tex, flags=re.S)
    return detex(match.group(1), macros_of(source, tex)) if match else ""


# ---------------------------------------------------------------------------------------------
# Reading the repository

def text_of(value):
    return " ".join(str(value).split()) if isinstance(value, (str, int, float)) else ""


def items_of(value):
    if value is None:
        return []
    return value if isinstance(value, list) else [value]


def registries():
    """The registered names and versions. A malformed registry gives empty results."""
    try:
        return ids.numbers("ideas"), ids.numbers("papers"), ids.versions()
    except ValueError as problem:
        warn(str(problem))
        return [], [], []


def load_ideas(numbers):
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
            "number": numbers.index(path.stem) + 1 if path.stem in numbers else None,
        })
    return sorted(ideas, key=lambda idea: (idea["number"] is None, idea["number"] or 0,
                                           idea["title"].lower()))


def describe(source):
    """The record of one state of a paper."""
    meta, problem = {}, ""
    record = source.text("meta.yaml")
    if record is None:
        problem = "meta.yaml is missing."
    else:
        try:
            loaded = yaml.safe_load(record)
            if isinstance(loaded, dict):
                meta = loaded
            else:
                problem = "meta.yaml is not a mapping."
        except yaml.YAMLError:
            problem = "meta.yaml could not be read."
    tex = source.text("paper.tex") or ""
    abstract = abstract_of(source, tex)
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
    keywords = [text_of(word) for word in items_of(meta.get("keywords")) if text_of(word)]
    if not keywords:
        # a record without keywords falls back on the keywords of the paper itself
        match = re.search(r"\\keywords\{([^{}]*)\}", tex)
        keywords = [" ".join(word.split()) for word in match.group(1).split(",")] if match else []
    verified = []
    for claim in items_of(meta.get("verified")):
        if isinstance(claim, dict):
            verified.append({key: text_of(claim.get(key)) for key in ("what", "by")})
    return {
        "title": text_of(meta.get("title")) or source.name,
        "idea": text_of(meta.get("idea")),
        "builds_on": [text_of(name) for name in items_of(meta.get("builds-on")) if text_of(name)],
        "changes": text_of(meta.get("changes")),
        "keywords": [word for word in keywords if word],
        "agents": [agent for agent in agents if agent["model"]],
        "humans": [human for human in humans if human["name"]],
        "verified": [claim for claim in verified if claim["what"]],
        "abstract": abstract,
        "summary": first_sentence(abstract),
        "problem": problem,
        "pdf": source.data("paper.pdf"),
        "tex": bool(tex),
        "artifact": source.has_directory("artifact"),
    }


def load_reviews(name):
    """The reviews of a paper. A file v<version>-<reviewer>.md reviews that version."""
    reviews = []
    folder = ROOT / "reviews" / name
    for path in sorted(folder.glob("*.md")) if folder.is_dir() else []:
        if not SLUG.fullmatch(path.stem):
            continue
        match = re.fullmatch(r"v(\d+)-(.+)", path.stem)
        reviews.append({
            "version": int(match.group(1)) if match else None,
            "reviewer": match.group(2) if match else path.stem,
            "body": read(path),
            "file": path.name,
        })
    return reviews


def load_papers(numbers, versions):
    papers = []
    folder = ROOT / "papers"
    for path in sorted(folder.iterdir()) if folder.is_dir() else []:
        if not path.is_dir():
            continue
        if not SLUG.fullmatch(path.name):
            warn(f"skipping papers/{path.name}: unexpected directory name")
            continue
        number = numbers.index(path.name) + 1 if path.name in numbers else None
        paper = describe(Source(path.name))
        if paper["problem"]:
            warn(f"papers/{path.name}: {paper['problem']}")
        recorded = [entry for entry in versions if entry[0] == number]
        head_tree = ids.git("rev-parse", "--verify", "--quiet", f"HEAD:papers/{path.name}")
        history = []
        for _, version, commit, tree, date in recorded:
            state = describe(Source(path.name, commit))
            if state["problem"] == "meta.yaml is missing." and not state["tex"]:
                warn(f"papers/{path.name}: version {version} is not in the git history here")
                continue
            # A human who is no longer named in the latest record is not named on the pages
            # of earlier versions either.
            named = {human["name"] for human in paper["humans"]}
            state["humans"] = [human for human in state["humans"] if human["name"] in named]
            state.update(version=version, commit=commit, date=date)
            history.append(state)
        paper.update(
            slug=path.name, number=number, history=history, reviews=load_reviews(path.name),
            version=recorded[-1][1] if recorded and recorded[-1][3] == head_tree else None)
        papers.append(paper)
    return sorted(papers, key=lambda paper: (paper["number"] is None, paper["number"] or 0,
                                             paper["title"].lower()))


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
<a href="{base}search.html">Search</a>
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


def redirect(target):
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta http-equiv="refresh" content="0; url={esc(target, quote=True)}">
<link rel="canonical" href="{esc(target, quote=True)}">
<title>{esc(SITE_NAME)}</title>
</head>
<body><p><a href="{esc(target, quote=True)}">Continue</a></p></body>
</html>
"""


def identifier(number, version=None):
    return f"{PREFIX}:{number}" + (f"v{version}" if version else "")


def label(number):
    return f'<span class="num">{number}</span> ' if number else ""


def byline(paper):
    """The models that wrote the paper. A paper without an agent is credited to its humans."""
    names = [agent["model"] for agent in paper["agents"]] or [human["name"] for human in paper["humans"]]
    return ", ".join(esc(name) for name in dict.fromkeys(names))


def paper_entry(paper, base):
    count = len(paper["verified"])
    facts = [byline(paper)]
    if paper["version"]:
        facts.append(f"version {paper['version']}")
    facts.append(f"{count} verified claim{'s' if count != 1 else ''}")
    if paper["builds_on"]:
        facts.append("builds on " + ", ".join(esc(name) for name in paper["builds_on"]))
    if paper["reviews"]:
        facts.append(f"{len(paper['reviews'])} review{'s' if len(paper['reviews']) != 1 else ''}")
    summary = f"<p>{esc(paper['summary'])}</p>" if paper["summary"] else ""
    return (f'<li>{label(paper["number"])}'
            f'<a class="title" href="{base}papers/{quote(paper["slug"])}/index.html">'
            f'{esc(paper["title"])}</a>{summary}'
            f'<p class="meta">{" · ".join(fact for fact in facts if fact)}</p></li>')


def idea_entry(idea, base, papers):
    grown = [paper for paper in papers if paper["idea"] == idea["slug"]]
    note = ""
    if grown:
        links = ", ".join(
            f'<a href="{base}papers/{quote(paper["slug"])}/index.html">{esc(paper["title"])}</a>'
            for paper in grown)
        note = f'<p class="meta">Realized by {links}</p>'
    summary = f"<p>{esc(idea['summary'])}</p>" if idea["summary"] else ""
    return (f'<li>{label(idea["number"])}'
            f'<a class="title" href="{base}ideas/{quote(idea["slug"])}.html">'
            f'{esc(idea["title"])}</a>{summary}{note}</li>')


def entries(items):
    return '<ul class="entries">\n' + "\n".join(items) + "\n</ul>" if items else "<p>None yet.</p>"


def home_page(ideas, papers):
    readme = read(ROOT / "README.md") if (ROOT / "README.md").is_file() else ""
    heading = re.search(r"^#\s+(.+?)\s*$", readme, flags=re.M)
    name = plain(heading.group(1)) if heading else SITE_NAME
    lead = first_sentence(readme[heading.end():] if heading else readme, limit=400)
    count = max([paper["number"] or 0 for paper in papers] + [0])
    body = f"""<h1>{esc(name)}</h1>
<p class="lead">{esc(lead)}</p>
<p class="progress"><strong>{count:,}</strong> of {GOAL:,} papers</p>
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
    kicker = f"Idea {idea['number']}" if idea["number"] else "Idea"
    body = f"""<p class="kicker">{kicker}</p>
<h1>{esc(idea["title"])}</h1>
{render_markdown(idea["body"], linker("ideas", base))}
{papers_html}
<p class="meta"><a href="{source}">Source of this idea</a></p>"""
    return page(idea["title"], body, base)


def record_rows(state, ideas, papers, base):
    rows = []
    known_ideas = {idea["slug"]: idea for idea in ideas}
    if state["idea"]:
        idea = known_ideas.get(state["idea"])
        value = (f'<a href="{base}ideas/{quote(idea["slug"])}.html">{esc(idea["title"])}</a>'
                 if idea else esc(state["idea"]))
        rows.append(("Idea", value))
    if state["keywords"]:
        rows.append(("Keywords", ", ".join(
            f'<a href="{base}search.html?q={quote(word)}">{esc(word)}</a>' for word in state["keywords"])))
    for agent in state["agents"]:
        value = esc(agent["model"])
        if agent["harness"]:
            value += f" in {esc(agent['harness'])}"
        if agent["did"]:
            value += f": {esc(agent['did'])}"
        rows.append(("Agent", value))
    for human in state["humans"]:
        value = esc(human["name"])
        if human["did"]:
            value += f": {esc(human['did'])}"
        rows.append(("Human", value))
    return "\n".join(f"<dt>{name}</dt><dd>{value}</dd>" for name, value in rows)


def demote(rendered):
    """Moves the headings of a rendered text below the headings of the page around it."""
    return re.sub(r"<(/?)h([1-6])>", lambda match: f"<{match.group(1)}h{min(6, int(match.group(2)) + 3)}>",
                  rendered)


def reference_list(names, papers, base):
    """The papers of this repository with the given names, as entries."""
    known = {paper["slug"]: paper for paper in papers}
    items = [paper_entry(known[name], base) if name in known
             else f"<li>{esc(name)} <span class=\"meta\">is not a paper of this repository</span></li>"
             for name in names]
    return entries(items)


def review_blocks(paper, reviews, base):
    blocks = []
    for review in reviews:
        about = f"Version {review['version']}, " if review["version"] else ""
        source = f"{REPO_URL}/blob/main/reviews/{quote(paper['slug'])}/{quote(review['file'])}"
        blocks.append(
            f'<section class="review"><h3>{about}reviewed by {esc(review["reviewer"])}</h3>\n'
            + demote(render_markdown(review["body"], linker(f"reviews/{paper['slug']}", base)))
            + f'\n<p class="meta"><a href="{source}">Source of this review</a></p></section>')
    return "\n".join(blocks)


def paper_body(paper, state, ideas, papers, base, version):
    """The page of a paper. `state` is the latest state, or the state of `version`."""
    slug = quote(paper["slug"])
    number = paper["number"]
    place = f"tree/{state['commit']}" if version else "tree/main"
    blob = f"blob/{state['commit']}" if version else "blob/main"
    folder = f"{REPO_URL}/{place}/papers/{slug}"
    actions = []
    if state["pdf"] is not None:
        actions.append('<a class="button" href="paper.pdf">Read the PDF</a>')
    if state["tex"]:
        actions.append(f'<a href="{REPO_URL}/{blob}/papers/{slug}/paper.tex">LaTeX source</a>')
    if state["artifact"]:
        actions.append(f'<a href="{folder}/artifact">Artifact</a>')
    actions.append(f'<a href="{folder}">All files</a>')
    shown = version or paper["version"]
    kicker = f"Paper {number}" if number else "Paper"
    if shown:
        kicker += f" · version {shown}"
    parts = [
        f'<p class="kicker">{kicker}</p>',
        f"<h1>{esc(state['title'])}</h1>",
        f'<p class="byline">{byline(state)}</p>' if byline(state) else "",
    ]
    latest = paper["history"][-1]["version"] if paper["history"] else None
    if version and latest and version != latest:
        parts.append(f'<p class="notice">This is version {version}. '
                     f'<a href="../index.html">Version {latest}</a> is the latest.</p>')
    if number:
        permanent = f"{SITE_URL}p/{number}/" + (f"v{shown}/" if shown else "")
        cite = identifier(number, shown)
        parts.append(f'<p class="meta">Identifier <code>{cite}</code>, permanent address '
                     f'<a href="{permanent}">{esc(permanent)}</a></p>')
    else:
        parts.append('<p class="meta">This paper has no number yet. '
                     "Numbers are assigned on the main branch.</p>")
    parts.append(f'<p class="actions">{" ".join(actions)}</p>')
    if state["problem"]:
        parts.append(f'<p class="meta">The record of this paper is incomplete: {esc(state["problem"])}</p>')
    if state["abstract"]:
        parts.append(f"<h2>Abstract</h2>\n<p>{esc(state['abstract'])}</p>")
    rows = record_rows(state, ideas, papers, base)
    if rows:
        parts.append(f'<h2>Record</h2>\n<dl class="record">\n{rows}\n</dl>')
    parts.append("<h2>Verified</h2>")
    if state["verified"]:
        claims = "\n".join(
            f"<tr><td>{esc(claim['what'])}</td><td><code>{esc(claim['by'])}</code></td></tr>"
            for claim in state["verified"])
        parts.append("<p>A command in the paper's directory checks each of these claims. "
                     "Every other claim of the paper is unverified.</p>\n"
                     f"<table><thead><tr><th>Claim</th><th>Checked by</th></tr></thead>\n"
                     f"<tbody>\n{claims}\n</tbody></table>")
    else:
        parts.append("<p>No claim of this paper is checked by a command.</p>")
    if state["builds_on"]:
        parts.append("<h2>References in this repository</h2>\n"
                     "<p>The papers that this paper builds on.</p>\n"
                     + reference_list(state["builds_on"], papers, base))
    if not version:
        citing = [other["slug"] for other in papers if paper["slug"] in other["builds_on"]]
        if citing:
            parts.append("<h2>Referenced by</h2>\n<p>The papers that build on this paper.</p>\n"
                         + reference_list(citing, papers, base))
    if paper["history"] and not version:
        lines = []
        for entry in reversed(paper["history"]):
            note = f" {esc(entry['changes'])}" if entry["changes"] and entry["version"] > 1 else ""
            lines.append(
                f'<li><a href="v{entry["version"]}/index.html">Version {entry["version"]}</a> '
                f'<span class="meta">{esc(entry["date"])} · <code>{identifier(number, entry["version"])}'
                f'</code> · commit <a href="{REPO_URL}/commit/{entry["commit"]}">'
                f'{entry["commit"][:7]}</a></span>{note}</li>')
        parts.append('<h2>Versions</h2>\n<ul class="versions">\n' + "\n".join(lines) + "\n</ul>")
    reviews = [review for review in paper["reviews"]
               if not version or review["version"] == version]
    if reviews:
        parts.append("<h2>Reviews</h2>\n" + review_blocks(paper, reviews, base))
    elif not version:
        parts.append('<h2>Reviews</h2>\n<p>No review yet. <a href="' + base
                     + 'contributing.html">How to review a paper</a></p>')
    if state["pdf"] is not None:
        parts.append('<h2>PDF</h2>\n<object class="pdf" data="paper.pdf" type="application/pdf">'
                     '<p>This browser does not show PDFs inline. '
                     '<a href="paper.pdf">Open the PDF</a>.</p></object>')
    return "\n".join(part for part in parts if part)


def search_index(ideas, papers):
    """Every paper and idea as data, for the search page and for agents."""
    entries = []
    for paper in papers:
        entries.append({
            "kind": "paper", "number": paper["number"],
            "id": identifier(paper["number"], paper["version"]) if paper["number"] else None,
            "name": paper["slug"], "title": paper["title"],
            "url": f"papers/{quote(paper['slug'])}/index.html",
            "authors": ([agent["model"] for agent in paper["agents"]]
                        or [human["name"] for human in paper["humans"]]),
            "keywords": paper["keywords"], "abstract": paper["abstract"], "idea": paper["idea"],
            "builds_on": paper["builds_on"], "verified": len(paper["verified"]),
        })
    for idea in ideas:
        entries.append({
            "kind": "idea", "number": idea["number"], "name": idea["slug"], "title": idea["title"],
            "url": f"ideas/{quote(idea['slug'])}.html", "text": plain(idea["body"]),
        })
    return json.dumps(entries, ensure_ascii=False, indent=1) + "\n"


SEARCH_SCRIPT = """
const box = document.getElementById("q");
const list = document.getElementById("results");
const note = document.getElementById("note");
let entries = [];
const words = e => [e.title, (e.keywords || []).join(" "), (e.authors || []).join(" "), e.id || "",
                    e.name, e.abstract || "", e.text || ""].join(" ").toLowerCase();
const front = e => (e.title + " " + (e.keywords || []).join(" ")).toLowerCase();
function show() {
  const terms = box.value.toLowerCase().split(/\\s+/).filter(Boolean);
  const score = e => terms.filter(t => front(e).includes(t)).length;
  const hits = entries.filter(e => terms.every(t => e.words.includes(t)));
  hits.sort((a, b) => score(b) - score(a) || (a.kind === b.kind ? 0 : a.kind === "paper" ? -1 : 1)
                      || (a.number || 1e15) - (b.number || 1e15));
  list.replaceChildren();
  for (const e of hits) {
    const item = document.createElement("li");
    const link = document.createElement("a");
    const meta = document.createElement("p");
    link.className = "title";
    link.href = e.url;
    link.textContent = e.title;
    meta.className = "meta";
    meta.textContent = (e.kind === "paper" ? "Paper" : "Idea") + (e.number ? " " + e.number : "")
      + (e.keywords && e.keywords.length ? " · " + e.keywords.join(", ") : "");
    item.append(link, meta);
    list.append(item);
  }
  note.textContent = terms.length ? hits.length + " of " + entries.length + " entries match."
                                  : entries.length + " entries.";
  const url = new URL(location);
  if (box.value) url.searchParams.set("q", box.value); else url.searchParams.delete("q");
  history.replaceState(null, "", url);
}
fetch("search.json").then(reply => reply.json()).then(data => {
  entries = data;
  for (const e of entries) e.words = words(e);
  box.value = new URLSearchParams(location.search).get("q") || "";
  show();
}).catch(() => { note.textContent = "The index could not be loaded."; });
box.addEventListener("input", show);
"""


def search_page():
    body = f"""<h1>Search</h1>
<p>Words are matched against titles, keywords, authors, identifiers, abstracts, and ideas.
An entry matches when every word occurs in it.</p>
<p><input id="q" class="search" type="search" placeholder="integrity agents" autofocus></p>
<p id="note" class="meta"></p>
<ul id="results" class="entries"></ul>
<p class="meta">The index is one file, <a href="search.json">search.json</a>. It lists every paper
and idea with its number, its keywords, and its abstract, so an agent can read it instead of the
pages.</p>
<script>{SEARCH_SCRIPT}</script>"""
    return page("Search", body, "")


def doc_page(name, title):
    path = ROOT / name
    text = read(path) if path.is_file() else f"# {title}\n\nThis file is missing."
    return page(title, render_markdown(text, linker("", "")), "")


def build(out):
    if out.exists():
        shutil.rmtree(out)
    (out / "ideas").mkdir(parents=True)
    (out / "papers").mkdir()
    idea_numbers, paper_numbers, versions = registries()
    ideas, papers = load_ideas(idea_numbers), load_papers(paper_numbers, versions)

    def write(relative, content):
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(content, bytes):
            target.write_bytes(content)
        else:
            target.write_text(content, encoding="utf-8")

    shutil.copyfile(ROOT / "site" / "style.css", out / "style.css")
    write("index.html", home_page(ideas, papers))
    write("rationale.html", doc_page("RATIONALE.md", "Rationale"))
    write("contributing.html", doc_page("CONTRIBUTING.md", "Contributing"))
    write("search.html", search_page())
    write("search.json", search_index(ideas, papers))
    write("ideas/index.html", page("Ideas", f"""<h1>Ideas <span class="count">{len(ideas)}</span></h1>
<p>An idea is a few sentences. Agents and humans pick ideas up and write them into papers.</p>
{entries([idea_entry(idea, "../", papers) for idea in ideas])}""", "../"))
    for idea in ideas:
        write(f"ideas/{idea['slug']}.html", idea_page(idea, papers))
        if idea["number"]:
            write(f"i/{idea['number']}/index.html", redirect(f"../../ideas/{quote(idea['slug'])}.html"))
    write("papers/index.html", page("Papers", f"""<h1>Papers <span class="count">{len(papers)}</span></h1>
<p>Each paper records who wrote it and which of its claims a command checks.</p>
{entries([paper_entry(paper, "../") for paper in papers])}""", "../"))
    for paper in papers:
        slug, number = paper["slug"], paper["number"]
        write(f"papers/{slug}/index.html",
              page(paper["title"], paper_body(paper, paper, ideas, papers, "../../", None), "../../"))
        if paper["pdf"] is not None:
            write(f"papers/{slug}/paper.pdf", paper["pdf"])
        if number:
            write(f"p/{number}/index.html", redirect(f"../../papers/{quote(slug)}/index.html"))
        for state in paper["history"]:
            version = state["version"]
            write(f"papers/{slug}/v{version}/index.html",
                  page(f"{state['title']} (version {version})",
                       paper_body(paper, state, ideas, papers, "../../../", version), "../../../"))
            if state["pdf"] is not None:
                write(f"papers/{slug}/v{version}/paper.pdf", state["pdf"])
            if number:
                write(f"p/{number}/v{version}/index.html",
                      redirect(f"../../../papers/{quote(slug)}/v{version}/index.html"))
    print(f"built {len(ideas)} ideas and {len(papers)} papers into {out}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    build(Path(sys.argv[1]).resolve())
