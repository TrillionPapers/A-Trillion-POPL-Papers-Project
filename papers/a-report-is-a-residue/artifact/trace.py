#!/usr/bin/env python3
"""Turns the record of a Claude Code session into the trace that owed.py replays.

    python3 trace.py <session.jsonl> > session.txt

The record is private and is not in this repository; the trace is.  A line of the trace is one
event: a letter, with the paper that it concerns, or one of the marks

    end        the agent ends its turn
    compact    the context is replaced by a summary
    registry   the registry of papers starts to exist (the rule about looking at it starts)

Only the names of the papers of this repository and the fixed words of this file appear in
the trace.  The messages of the user leave no mark in it.  The letters are

    edit p     a source of the PDF of paper p is written (paper.tex, refs.bib)
    code p     a source of the artifact of paper p is written
    tex p      the paper is compiled and a PDF comes out
    run p      the artifact is run (make check, make all, lean, or its script)
    commit p   a commit that contains files of paper p; `commit -` contains none
    push, pull, stash, pop
    look       the registry is read, or a page of the site is fetched by its number

They come from the tool calls of the main agent; calls made by sub-agents are not in the
record that this script reads.  A shell command is cut into its parts, in order.  The patterns
below decide what a part did.  They were written against the commands of one session and
checked by reading the commands next to the events; another session needs other patterns.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAPERS = [p for p in sorted(os.listdir(os.path.join(HERE, '..', '..'))) if re.fullmatch(r'[a-z0-9-]+', p)]


def paper_of(path):
    m = re.search(r'papers/([a-z0-9-]+)', path)
    return m.group(1) if m and m.group(1) in PAPERS else None


def kind_of(path):
    if not paper_of(path):
        return None
    if re.search(r'/(paper\.tex|refs\.bib)$', path):
        return 'edit'
    if '/artifact/' in path and '/expected/' not in path and '/out/' not in path:
        return 'code'
    return None


HEREDOC = re.compile(r"<<-?\s*['\"]?(\w+)['\"]?[^\n]*\n(.*?)\n\1\b", re.S)
ASSIGN = re.compile(r'(?:^|[;&|\n(]\s*)([A-Za-z_]\w*)=("[^"\n]*"|[^\s;&|)]*)')
GROUP = re.compile(r'\(\s*cd\s+("[^"\n]*"|[^\s;&|)]+)\s*(?:&&|;)([^()]*)\)')
PARTS = [
    ('cd', re.compile(r'\bcd\s+("[^"\n]*"|[^\s;&|)]+)')),
    ('tex', re.compile(r'latexmk\s+-pdf')),
    ('run', re.compile(r'make\s+(?:-C\s+(\S+)\s+)?(?:check|all)\b()')),
    ('run', re.compile(r'\blean\s+()([\w./"$-]+\.lean)\b(?!\s*<<)')),
    ('run', re.compile(r'\bpython3?\s+()([\w./"$-]+\.py)\b')),
    ('ship', re.compile(r'ship\.sh"?\s+([a-z0-9-]+)')),
    ('add', re.compile(r'git add\s+([^;&|\n]+)')),
    ('commit', re.compile(r'git commit')),
    ('pop', re.compile(r'git stash pop')),
    ('stash', re.compile(r'git stash(?! pop)')),
    ('pull', re.compile(r'git pull')),
    ('push', re.compile(r'git push')),
    ('look', re.compile(r'(?:tail|cat|head|grep)\b[^;&|\n]*papers/(?:REGISTRY|VERSIONS)|curl[^;&|\n]*/p/\d+')),
    ('write', re.compile(r'>\s*("[^"\n]*"|[^\s;&|<>]+)\s*<<')),
    ('write', re.compile(r'(?:sed -i\S*|perl -pi\S*)[^;&|\n]*?([\w./"$-]+\.(?:tex|bib|py|lean))')),
]
PYWRITE = re.compile(r"""open\(\s*f?['"]([^'"]+)['"]\s*,\s*['"][wa]|['"]([^'"]+)['"]\)?\.write_text""")
TEX_FAILED = re.compile(r'Fatal error occurred|no output PDF|LaTeX Error|Emergency stop|Couldn.t open file .paper\.pdf')


def shell(command, cwd, output):
    """The events of one shell command, in the order of its parts."""
    bodies = [(m.start(2), m.group(2)) for m in HEREDOC.finditer(command)]
    flat = HEREDOC.sub(lambda m: m.group(0)[:m.start(2) - m.start()] + ' ' * len(m.group(2))
                       + m.group(0)[m.end(2) - m.start():], command)
    found = [(m.start(), name, m) for name, pat in PARTS for m in pat.finditer(flat)]
    found += [(m.start(), 'let', m) for m in ASSIGN.finditer(flat)]
    found += [(start, 'pywrite', m) for start, body in bodies for m in PYWRITE.finditer(body)]
    groups = [(m.start(), m.end(), m.group(1)) for m in GROUP.finditer(flat)]
    found.sort(key=lambda x: x[0])
    env, here, events, staged = {}, cwd, [], []

    def value(text):
        text = text.strip('"')
        for _ in range(3):
            text = re.sub(r'\$\{?(\w+)\}?', lambda m: env.get(m.group(1), m.group(0)), text)
        return text

    def at(pos):
        """The directory in which the part at `pos` runs."""
        for start, end, target in groups:
            if start < pos < end:
                return os.path.normpath(os.path.join(here, value(target)))
        return here

    for pos, name, m in found:
        if name == 'let':
            env[m.group(1)] = value(m.group(2))
        elif name == 'cd':
            if not any(start < pos < end for start, end, _ in groups):
                here = os.path.normpath(os.path.join(here, value(m.group(1))))
        elif name == 'tex':
            p = paper_of(at(pos) + '/')
            if p and not TEX_FAILED.search(output):
                events.append(('tex', p))
        elif name == 'run':
            where = at(pos)
            target = os.path.join(where, value(m.group(1) or '.'), value(m.group(2) or ''))
            p = paper_of(os.path.normpath(target) + '/')
            if p and '/artifact' in os.path.normpath(target) + '/':
                events.append(('run', p))
        elif name == 'ship':
            p = m.group(1)
            if p in PAPERS and not TEX_FAILED.search(output):
                events.append(('tex', p))
                if 'fix the layout' not in output and 'make check FAILED' not in output:
                    events += [('run', p), ('commit', p)]
                    if 'cannot pull' not in output:
                        events += [('pull', None), ('push', None)]
        elif name == 'add':
            for x in m.group(1).split():
                x = value(x)
                if 'papers/REGISTRY' in x:
                    events.append(('registry', None))
                staged.append(paper_of(x + '/') or ('*' if x.rstrip('/') in ('papers', '-A', '.') else None))
        elif name == 'commit':
            ps = sorted({p for p in staged if p})
            events += [('commit', p) for p in ps] or [('commit', '-')]
            staged = []
        elif name in ('pull', 'push', 'stash', 'pop', 'look'):
            events.append((name, None))
        else:
            path = os.path.normpath(os.path.join(at(pos), value(next(g for g in m.groups() if g))))
            if kind_of(path):
                events.append((kind_of(path), paper_of(path)))
    return events


def read(record):
    """The marks and the tool calls of the main agent, in order, with the results of the calls."""
    results, order = {}, []
    for line in open(record):
        d = json.loads(line)
        t, m = d.get('type'), d.get('message')
        if t == 'system' and d.get('subtype') == 'compact_boundary':
            order.append(('mark', 'compact'))
        if not isinstance(m, dict):
            continue
        c = m.get('content')
        if t == 'user' and not d.get('isCompactSummary') and not d.get('isMeta'):
            if isinstance(c, str):
                continue                    # what the user wrote is not part of the trace
            for b in c:
                if b.get('type') == 'tool_result':
                    cc = b.get('content')
                    text = cc if isinstance(cc, str) else ' '.join(x.get('text', '') for x in cc if isinstance(x, dict))
                    results[b['tool_use_id']] = (bool(b.get('is_error')), text)
        elif t == 'assistant' and isinstance(c, list):
            for b in c:
                if b.get('type') == 'tool_use':
                    order.append(('use', b['id'], b['name'], b.get('input', {}), d.get('cwd', '')))
            if m.get('stop_reason') == 'end_turn':
                order.append(('mark', 'end'))
    return order, results


def events_of(record):
    order, results = read(record)
    seen, calls = [], 0
    for item in order:
        if item[0] == 'mark':
            yield item[1], None, calls
            continue
        _, id_, name, inp, cwd = item
        calls += 1
        failed, output = results.get(id_, (False, ''))
        if '<tool_use_error>' in output:
            continue                        # the call was refused before it ran
        if name in ('Write', 'Edit'):
            k = kind_of(inp.get('file_path', ''))
            events = [(k, paper_of(inp['file_path']))] if k else []
        elif name == 'Bash':
            events = shell(inp.get('command', ''), cwd, output)
        else:
            events = []
        for letter, p in events:
            if p == '*':
                for q in seen:
                    yield letter, q, calls
                continue
            if p and p != '-' and p not in seen:
                seen.append(p)
            yield letter, p, calls


if __name__ == '__main__':
    compacts = 0
    for letter, p, calls in events_of(sys.argv[1]):
        if len(sys.argv) > 2:
            print(letter + (' ' + p if p else '') + '   # call %d' % calls)
        else:
            print(letter + (' ' + p if p else ''))
        compacts += letter == 'compact'
        if compacts == 3:
            break                           # the study ends when the eleventh paper is out
