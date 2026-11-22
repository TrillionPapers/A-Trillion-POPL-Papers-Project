#!/usr/bin/env python3
"""Checks talks against the part of the standard in CONVENTIONS.md that a program can check.

    python site/check_talk.py              every talk under talks/
    python site/check_talk.py FILE ...     these talks

A talk names the standard it was made to in a comment on its first line,

    <!-- standard: 2026-11-22 -->

and it is checked against that one. A talk that names none is checked against the standard in
force. The exit status is 1 if a talk fails. Needs python3 and nothing else.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IN_FORCE = "2026-11-22"
STATE = re.compile(r"^(in|out|s\d+|c\d+-\d+|current|past|hot|faded|w)$")


def strip_comments(css):
    """A style sheet without its comments, and without the addresses in url(...), which have
    dots that are not classes."""
    return re.sub(r"url\([^)]*\)", "url()", re.sub(r"/\*.*?\*/", "", css, flags=re.S))


def words_of(html):
    return re.sub(r"<[^>]+>", "", html).split()


def standard_2026_11_22(text, kit):
    """The checks of the standard of 22 November 2026. Returns problems and notes."""
    problems, notes = [], []
    css = strip_comments("\n".join(re.findall(r"<style[^>]*>(.*?)</style>", text, flags=re.S)))
    body = re.sub(r"<style[^>]*>.*?</style>", "", text, flags=re.S)
    kit = strip_comments(kit)
    kit_classes = set(re.findall(r"\.([A-Za-z_][\w-]*)", kit))
    own_classes = set(re.findall(r"\.([A-Za-z_][\w-]*)", css))
    used = set()
    for match in re.finditer(r'class="([^"]*)"', body):
        used.update(match.group(1).split())
    ids = set(re.findall(r'\bid="([^"]*)"', body))

    # every class on an element is known, and every rule of the talk has something to style
    unknown = sorted(name for name in used if name not in kit_classes and name not in own_classes)
    if unknown:
        problems.append(f"classes that no rule knows: {', '.join(unknown)}")
    for selector in re.findall(r"(?m)^([^{}@\n][^{}]*)\{", css):
        for name in re.findall(r"\.([A-Za-z_][\w-]*)", selector):
            if name not in used and not STATE.match(name):
                problems.append(f"a rule for the class “{name}”, which no element has: {selector.strip()[:60]}")
        for name in re.findall(r"#([A-Za-z_][\w-]*)", selector):
            if name not in ids:
                problems.append(f"a rule for the scene “{name}”, which does not exist: {selector.strip()[:60]}")
        # a note, not a problem: a rule that restyles a class of the stage sheet for a whole scene
        parts = selector.strip().split()
        if len(parts) == 2 and re.fullmatch(r"#[\w-]+(\.[sc][\d-]+)*", parts[0]):
            bare = re.fullmatch(r"\.([A-Za-z_][\w-]*)", parts[1])
            if bare and bare.group(1) in kit_classes:
                notes.append(f"“{selector.strip()}” restyles a class of the stage sheet for the whole scene")

    # every animation has its keyframes
    defined = set(re.findall(r"@keyframes\s+([\w-]+)", css)) | set(re.findall(r"@keyframes\s+([\w-]+)", kit))
    for name in set(re.findall(r"animation:\s*([\w-]+)", css + body)) - defined - {"none"}:
        problems.append(f"the animation “{name}” has no keyframes")

    scenes = re.findall(r"<section\b[^>]*>.*?</section>", body, flags=re.S)
    if not scenes:
        problems.append("no scenes")
    total = 0
    for number, scene in enumerate(scenes, 1):
        tag = scene[:scene.index(">") + 1]
        name = (re.search(r'\bid="([^"]*)"', tag) or [None, f"scene {number}"])[1]
        classes = (re.search(r'class="([^"]*)"', tag) or [None, ""])[1].split()
        if "scene" not in classes:
            problems.append(f"{name}: a section without the class “scene”")
        if "deep" not in classes:
            problems.append(f"{name}: not in the look of the standard (class “deep”)")
        if not re.search(r'data-title="[^"]+"', tag):
            problems.append(f"{name}: no data-title")
        lines = [len(words_of(line)) for line in re.findall(r"<p>(.*?)</p>", scene, flags=re.S)]
        total += sum(lines)
        if not lines:
            problems.append(f"{name}: nothing is said")
        for line in lines:
            if line > 40:
                problems.append(f"{name}: a line of {line} words; some voices stop in the middle of one over 40")
        listed = set((re.search(r'data-cues="([^"]*)"', tag) or [None, ""])[1].split())
        if re.search(r'\bid="', tag):
            wanted = {cue.replace("-", ":") for cue in re.findall(rf"#{re.escape(name)}\.c(\d+-\d+)", css)}
            for cue in sorted(wanted - listed):
                problems.append(f"{name}: a rule uses the cue {cue}, which data-cues does not list")
            for cue in sorted(listed - wanted):
                problems.append(f"{name}: data-cues lists {cue}, which no rule uses")
            for step in {int(n) for n in re.findall(rf"#{re.escape(name)}\.s(\d+)", css)}:
                if step > len(lines):
                    problems.append(f"{name}: a rule uses line {step} of {len(lines)}")
        marks = re.findall(r'data-(?:in|out|fade)="([^"]*)"', scene) + sorted(listed)
        for mark in marks:
            first, _, second = mark.partition(":")
            if not first.isdigit() or (second and not second.isdigit()):
                problems.append(f"{name}: “{mark}” is not a mark")
                continue
            line, word = int(first), int(second or 0)
            if not 1 <= line <= len(lines) or word > lines[line - 1]:
                problems.append(f"{name}: the mark {mark} names no word of the scene")
        for match in re.finditer(r'class="[^"]*\bsync\b[^"]*" data-in="(\d+):(\d+)"[^>]*>(.*?)</div>', scene, flags=re.S):
            line, word, shown = int(match.group(1)), int(match.group(2)), words_of(match.group(3))
            if 1 <= line <= len(lines) and word + len(shown) - 1 > lines[line - 1]:
                problems.append(f"{name}: the text “{' '.join(shown)}” runs past the end of its line")
    if scenes and not 400 <= total <= 540:
        problems.append(f"{total} words; about two and a half minutes is 450 to 500")
    return problems, notes, total, len(scenes)


STANDARDS = {"2026-11-22": standard_2026_11_22}


def check(path, kit):
    text = path.read_text(encoding="utf-8")
    named = re.match(r"\s*<!--\s*standard:\s*([\d-]+)\s*-->", text)
    standard = named.group(1) if named else IN_FORCE
    if standard not in STANDARDS:
        return [f"names the standard {standard}, which is unknown"], [], 0, 0, standard
    return (*STANDARDS[standard](text, kit), standard)


def main(arguments):
    kit = (ROOT / "site" / "talk-scene.css").read_text(encoding="utf-8")
    paths = [Path(argument) for argument in arguments] or sorted((ROOT / "talks").glob("*/*.html"))
    failed = 0
    for path in paths:
        problems, notes, words, scenes, standard = check(path, kit)
        try:
            shown = path.resolve().relative_to(ROOT)
        except ValueError:
            shown = path
        print(f"{shown}: {scenes} scenes, {words} words, standard of {standard}: "
              + ("ok" if not problems else f"{len(problems)} problems"))
        for problem in problems:
            print(f"  problem: {problem}")
        for note in notes:
            print(f"  note: {note}")
        failed += bool(problems)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
