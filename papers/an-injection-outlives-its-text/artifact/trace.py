#!/usr/bin/env python3
"""Turns the record of a Claude Code session into the trace that outlives.py replays.

    python3 trace.py <session.jsonl> > session.txt

The record is private and is not in this repository; the trace is.  A line of the trace is one
tool call of the main agent, reduced to one of three words, or a mark:

    read       the call brings text into the context that somebody outside wrote: `read lookup`
               for the answer of a server of bibliographic records, `read agent` for the
               report of a sub-agent, `read page` for a search of the web or a page
    act        the call changes something outside the machine: a push, by hand or by the
               script that ships a paper, or a request to the hosting service that creates
               or changes something
    step       any other call
    compact    the context is replaced by a summary
    end        the agent ends its turn

Nothing else is in the trace, and the messages of the user leave no mark in it.  The trace
ends with the third summary, as the trace of the paper on obligations does.
"""
import json
import re
import sys

OWN = ('trillionpapers.github.io', 'github.com/TrillionPapers', 'localhost', '127.0.0.1')
LOOKUP = ('doi.org', 'api.crossref.org', 'export.arxiv.org', 'api.semanticscholar.org', 'api.openalex.org')
FETCH = re.compile(r'\b(?:curl|wget)\b[^;&|\n]*?https?://([^\s"\'/]+(?:/[^\s"\']*)?)')
ACT = re.compile(r'git push|ship\.sh"?\s+[a-z]|gh repo create|gh api[^;&|\n]*(?:-X\s*(?:POST|PUT|PATCH|DELETE)|\s-f\s|\s-F\s)'
                 r'|gh workflow run|gh secret')


def kind(name, inp):
    """`read lookup` is the answer of a server of bibliographic records, `read agent` the report
    of a sub-agent, `read page` any other text from outside."""
    if name == 'Agent':
        return 'read agent'
    if name in ('WebFetch', 'WebSearch') or name.startswith(('mcp__Claude_Browser', 'mcp__claude-in-chrome')):
        return 'read page'
    if name == 'Bash':
        command = inp.get('command', '')
        if ACT.search(command):
            return 'act'
        urls = [url for url in FETCH.findall(command) if not url.startswith(OWN)]
        if urls:
            return 'read lookup' if all(url.startswith(LOOKUP) for url in urls) else 'read page'
    return 'step'


def main(record):
    compacts = 0
    for line in open(record):
        d = json.loads(line)
        if d.get('type') == 'system' and d.get('subtype') == 'compact_boundary':
            print('compact')
            compacts += 1
            if compacts == 3:
                return
        m = d.get('message')
        if d.get('type') != 'assistant' or not isinstance(m, dict) or not isinstance(m.get('content'), list):
            continue
        for b in m['content']:
            if b.get('type') == 'tool_use':
                print(kind(b['name'], b.get('input', {})))
        if m.get('stop_reason') == 'end_turn':
            print('end')


if __name__ == '__main__':
    main(sys.argv[1])
