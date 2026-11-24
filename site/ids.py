#!/usr/bin/env python3
"""Sequence numbers and versions.

Usage: python site/ids.py assign | check

Every idea, every paper, and every oracle has a sequence number. The three kinds are counted
separately, from 1, in the order in which they reached the main branch. Every paper also has
versions, counted from 1. A version is a state of the paper's directory on the main branch.

  ideas/REGISTRY    one line per idea:     <number> <name>
  papers/REGISTRY   one line per paper:    <number> <name>
  oracles/REGISTRY  one line per oracle:   <number> <name>
  papers/VERSIONS   one line per version:  <number> <version> <commit> <tree> <date>

`assign` appends what is new and never touches an existing line. Only the workflow on the main
branch runs it, one run at a time, on the latest commit. So no number is given twice, and a
version always names one state of a paper. `check` verifies the four files and changes
nothing.
"""

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")
HASH = re.compile(r"[0-9a-f]{40}([0-9a-f]{24})?")
DATE = re.compile(r"\d{4}-\d{2}-\d{2}")
KINDS = ("ideas", "papers", "oracles")
FLAT = ("ideas", "oracles")     # a contribution of these kinds is one Markdown file
FILES = ("ideas/REGISTRY", "papers/REGISTRY", "oracles/REGISTRY", "papers/VERSIONS")


def git(*args):
    """The output of a git command, or None when it fails."""
    try:
        done = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True,
                              check=True)
    except (OSError, subprocess.CalledProcessError):
        return None
    return done.stdout.strip()


def names_on_disk(kind):
    folder = ROOT / kind
    if not folder.is_dir():
        return []
    if kind in FLAT:
        found = [path.stem for path in folder.glob("*.md")]
    else:
        found = [path.name for path in folder.iterdir() if path.is_dir()]
    return sorted(name for name in found if NAME.fullmatch(name))


def parse_numbers(text, label):
    """The names of a registry in order. The line of a name is its number."""
    names = []
    for index, line in enumerate(text.splitlines(), start=1):
        match = re.fullmatch(r"(\d+) (\S+)", line)
        if not match or match.group(1) != str(index) or not NAME.fullmatch(match.group(2)):
            raise ValueError(f"{label} line {index}: expected '{index} <name>'")
        names.append(match.group(2))
    if len(set(names)) != len(names):
        raise ValueError(f"{label}: a name has two numbers")
    return names


def parse_versions(text, papers):
    """The versions in order, as tuples (paper number, version, commit, tree, date)."""
    versions, last = [], {}
    for index, line in enumerate(text.splitlines(), start=1):
        parts = line.split(" ")
        if (len(parts) != 5 or not parts[0].isdigit() or not parts[1].isdigit()
                or not HASH.fullmatch(parts[2]) or not HASH.fullmatch(parts[3])
                or not DATE.fullmatch(parts[4])):
            raise ValueError(f"papers/VERSIONS line {index}: "
                             "expected '<number> <version> <commit> <tree> <date>'")
        number, version = int(parts[0]), int(parts[1])
        if not 1 <= number <= papers:
            raise ValueError(f"papers/VERSIONS line {index}: no paper has the number {number}")
        if version != last.get(number, 0) + 1:
            raise ValueError(f"papers/VERSIONS line {index}: the versions of paper {number} "
                             "are not 1, 2, 3, and so on")
        last[number] = version
        versions.append((number, version, parts[2], parts[3], parts[4]))
    return versions


def read(relative):
    path = ROOT / relative
    return path.read_text(encoding="utf-8") if path.is_file() else ""


def numbers(kind):
    return parse_numbers(read(f"{kind}/REGISTRY"), f"{kind}/REGISTRY")


def versions():
    return parse_versions(read("papers/VERSIONS"), len(numbers("papers")))


def check():
    """Raises ValueError when a registry is malformed or an existing line has changed."""
    for kind in KINDS:
        numbers(kind)
    versions()
    base = os.environ.get("IDS_BASE", "")
    if base and git("cat-file", "-e", f"{base}^{{commit}}") is not None:
        for relative in FILES:
            before = git("show", f"{base}:{relative}")
            if before and not read(relative).startswith(before + "\n"):
                raise ValueError(f"{relative}: a line that was already recorded has changed")


def arrival_order(kind, names):
    """Sorts names by the commit of the main branch that added them, then by name."""
    log = git("log", "--first-parent", "--reverse", "--diff-filter=A", "--name-only",
              "--format=%x00", "--", kind) or ""
    position, commit = {}, 0
    for line in log.splitlines():
        if line.startswith("\x00"):
            commit += 1
            continue
        parts = line.split("/")
        if len(parts) < 2 or parts[0] != kind:
            continue
        if kind in FLAT:
            name = parts[1][:-3] if len(parts) == 2 and parts[1].endswith(".md") else None
        else:
            name = parts[1] if len(parts) > 2 else None
        if name is not None:
            position.setdefault(name, commit)
    return sorted(names, key=lambda name: (position.get(name, sys.maxsize), name))


def append(relative, lines):
    """Appends lines to a registry. A registry that does not exist yet is created with its
    folder, even when it gets no line, so that all four files exist after the first run."""
    (ROOT / relative).parent.mkdir(exist_ok=True)
    with open(ROOT / relative, "a", encoding="utf-8") as registry:
        for line in lines:
            registry.write(line + "\n")
            print(f"{relative}: {line}")


def assign():
    check()
    for kind in KINDS:
        registered = numbers(kind)
        known = set(registered)
        new = arrival_order(kind, [name for name in names_on_disk(kind) if name not in known])
        append(f"{kind}/REGISTRY",
               [f"{len(registered) + offset} {name}" for offset, name in enumerate(new, start=1)])
    head = git("rev-parse", "HEAD")
    date = git("show", "-s", "--format=%cs", "HEAD")
    if not head or not date:
        return
    last = {}
    for number, version, _, tree, _ in versions():
        last[number] = (version, tree)
    lines = []
    for number, name in enumerate(numbers("papers"), start=1):
        tree = git("rev-parse", "--verify", "--quiet", f"HEAD:papers/{name}")
        if not tree:
            continue
        version, recorded = last.get(number, (0, None))
        if tree != recorded:
            lines.append(f"{number} {version + 1} {head} {tree} {date}")
    append("papers/VERSIONS", lines)
    check()


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in ("assign", "check"):
        sys.exit(__doc__)
    try:
        assign() if sys.argv[1] == "assign" else check()
    except ValueError as problem:
        sys.exit(f"error: {problem}")
