#!/usr/bin/env python3
"""Audits where the numbers in the papers of this repository come from, for "A Number Is a
Claim".

The file has four parts.

1. Reading a paper: the macros that its artifact generates, and the prose with its numerals.
2. The audit of one version of a paper: every quantity in the prose is bound to the artifact,
   or it repeats a generated value, or it repeats a literal of the artifact's source, or
   nothing supports it.
3. The versions that are audited, read from the history of the repository with git.
4. The rendering semantics of the paper's calculus (Section 3), with tests of its theorems,
   and the tests.  `python3 evidence.py out` writes out/check.txt, out/numbers.tex and
   out/unsupported.txt.  It needs git and the history of the repository.
"""
import os
import random
import re
import subprocess
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, '..', '..', '..'))


# ---------------------------------------------------------------------------------------------
# 1. Reading a paper
# ---------------------------------------------------------------------------------------------

WORDS = {'two': 2, 'three': 3, 'four': 4, 'five': 5, 'six': 6, 'seven': 7, 'eight': 8, 'nine': 9,
         'ten': 10, 'eleven': 11, 'twelve': 12, 'thirteen': 13, 'fourteen': 14, 'fifteen': 15,
         'sixteen': 16, 'twenty': 20, 'thirty': 30, 'forty': 40, 'fifty': 50, 'sixty': 60,
         'hundred': 100, 'thousand': 1000, 'million': 1000000}
PARTS = ('half', 'third', 'thirds', 'quarter', 'quarters', 'fifth', 'sixth', 'eighth', 'tenth',
         'sixteenth', 'twice', 'double', 'doubles')
SMALL = 12          # a whole number up to here is a count of things, not a measurement
NUMERAL = r'\d+(?:,\d{3})*(?:\.\d+)?'


def balanced(s, i):
    """The index after the group in braces that opens at s[i]."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == '{' and s[j - 1:j] != '\\':
            depth += 1
        elif s[j] == '}' and s[j - 1:j] != '\\':
            depth -= 1
            if depth == 0:
                return j + 1
    return len(s)


def drop(s, command):
    """The text without a command and its argument in braces."""
    out, i = [], 0
    for m in re.finditer(r'\\' + command + r'\*?(?:\[[^\]]*\])?\{', s):
        if m.start() < i:
            continue
        out.append(s[i:m.start()])
        i = balanced(s, m.end() - 1)
        out.append(' ')
    return ''.join(out) + s[i:]


def value(numeral):
    return Fraction(numeral.replace('{,}', '').replace(',', ''))


def generated(tex, files):
    """The macros of the files that the paper inputs and that consist of \\newcommand lines:
    name -> value as text."""
    macros = {}
    for path in re.findall(r'\\input\{([^}]+)\}', tex):
        path = path if path.endswith('.tex') else path + '.tex'
        for line in files.get(path, '').splitlines():
            m = re.match(r'\\newcommand\{\\([A-Za-z]+)\}\{(.*)\}\s*$', line)
            if m:
                macros[m.group(1)] = m.group(2)
    return macros


def prose(tex):
    """The body of a paper as pieces ('text' | 'math' | 'cell', content): what a reader reads
    as prose and as entries of tables.  Figures, displays of programs and rules, labels,
    references, citations and code are left out, and their numerals are counted as formal."""
    body = tex[tex.index('\\begin{document}'):]
    body = re.split(r'\\bibliographystyle|\\end\{document\}', body)[0]
    body = re.sub(r'(?<!\\)%.*', '', body)
    for command in ('Description', 'label', 'ref', 'citep', 'citet', 'cite', 'input', 'texttt', 'url',
                    'vspace', 'hspace', 'includegraphics', 'bibliography', 'author'):
        body = drop(body, command)
    body = re.sub(r'\\\\\[[^\]]*\]', r'\\\\', body)
    pieces, formal = [], 0

    def numerals(s):
        return len(re.findall(NUMERAL, s.replace('{,}', ',')))

    def take(env_body, kind):
        nonlocal formal
        rest = env_body
        while True:
            m = re.search(r'\\caption\{', rest)
            if not m:
                break
            end = balanced(rest, m.end() - 1)
            pieces.append(('caption', rest[m.end():end - 1]))
            rest = rest[:m.start()] + ' ' + rest[end:]
        if kind == 'table':
            for tab in re.findall(r'\\begin\{tabular\}\{.*?\}\n(.*?)\\end\{tabular\}', rest, flags=re.S):
                tab = re.sub(r'\\(toprule|midrule|bottomrule)', ' ', tab)
                for cell in re.split(r'&|\\\\', tab):
                    if cell.strip():
                        pieces.append(('cell', cell.strip()))
        else:
            formal += numerals(rest)

    out, i = [], 0
    for m in re.finditer(r'\\begin\{(figure|table|prog|mathpar)\}(.*?)\\end\{\1\}', body, flags=re.S):
        out.append(body[i:m.start()])
        take(m.group(2), m.group(1))
        i = m.end()
    body = ''.join(out) + body[i:]
    for m in re.finditer(r'\\\[(.*?)\\\]', body, flags=re.S):
        formal += numerals(m.group(1))
    body = re.sub(r'\\\[.*?\\\]', ' ', body, flags=re.S)
    captions = [content for kind, content in pieces if kind == 'caption']
    pieces = [piece for piece in pieces if piece[0] != 'caption']
    for chunk in [body] + captions:
        for j, part in enumerate(re.split(r'(?<!\\)\$', chunk)):
            pieces.append(('math' if j % 2 else 'text', part))
    return pieces, formal


# ---------------------------------------------------------------------------------------------
# 2. The audit
# ---------------------------------------------------------------------------------------------

PURE = re.compile(r'^[\d\s{},./+*\-=]*(?:\\(?:times|cdot|approx|%|,|;|!)[\d\s{},./+*\-=]*)*$')
PARAMETER = re.compile(r'^\s*\\?[A-Za-z]+(?:_\{?\w+\}?|\^\\ast)?\s*(?:=|<|>|\\le|\\ge|\\approx)\s*'
                       r'([\d{},.]+(?:\s*/\s*[\d{},.]+)?)\s*$')


class Audit:
    """The quantities of one version of a paper, by where they come from."""

    def __init__(self, tex, files):
        self.macros = generated(tex, files)
        self.values = set()
        for text in self.macros.values():
            try:
                self.values.add(value(text))
            except (ValueError, ZeroDivisionError):
                pass
        sources = '\n'.join(content for path, content in files.items()
                            if path.endswith(('.py', '.lean', 'Makefile', '.sh')))
        self.literals = {Fraction(x) for x in re.findall(r'(?<![\w.])\d+(?:\.\d+)?(?![\w.])', sources)}
        # a quotient of two literals, as in Fraction(1, 20) or 1 / 20, is a literal as well
        for m in re.finditer(r'Fraction\((\d+), (\d+)\)|(?<![\w.])(\d+) / (\d+)(?![\w.])', sources):
            a, b = (m.group(1), m.group(2)) if m.group(1) else (m.group(3), m.group(4))
            if int(b):
                self.literals.add(Fraction(int(a), int(b)))
        self.redefined = sorted(set(re.findall(r'\\(?:re)?newcommand\{\\([A-Za-z]+)\}|\\def\\([A-Za-z]+)', tex))
                                and {a or b for a, b in re.findall(
                                    r'\\(?:re)?newcommand\{\\([A-Za-z]+)\}|\\def\\([A-Za-z]+)', tex)}
                                & set(self.macros))
        self.bound = self.small = self.words = self.parts = 0
        self.around = ''
        outputs = '\n'.join(content for path, content in files.items()
                            if path.endswith('.txt') and path not in ('artifact/expected/numbers.tex',))
        self.recorded = {Fraction(x.replace(',', ''))
                         for x in re.findall(r'(?<![\w.])\d[\d,]*(?:\.\d+)?(?![\w])', outputs)}
        self.used = [name for name in re.findall(r'\\([A-Za-z]+)', tex) if name in self.macros]
        self.repeats, self.copied, self.parameters, self.unsupported = [], [], [], []
        pieces, self.formal = prose(tex)
        for kind, content in pieces:
            self.bound += sum(name in self.macros for name in re.findall(r'\\([A-Za-z]+)', content))
            content = re.sub(r'\\[A-Za-z]+', lambda m: ' ' if m.group(0)[1:] in self.macros else m.group(0),
                             content)
            if kind == 'math':
                flat = content.replace('{,}', ',')
                m = PARAMETER.match(flat)
                if PURE.match(flat):
                    self.quantities(re.finditer(NUMERAL, flat), flat, self.around)
                elif m:
                    self.quantities(re.finditer(NUMERAL, m.group(1)), flat, self.around)
                else:
                    self.formal += len(re.findall(NUMERAL, flat))
            else:
                text = content.replace('{,}', ',')
                self.around = ' '.join(text.split())[-60:]
                self.quantities(re.finditer(r'(?<![\w\\.^_])' + NUMERAL + r'(?![\w])', text), text, None)
                for word in re.findall(r'[A-Za-z]+', text):
                    if word.lower() in WORDS:
                        if WORDS[word.lower()] > SMALL:
                            self.words += 1
                    elif word.lower() in PARTS:
                        self.parts += 1

    def quantities(self, numerals, context, before):
        for m in numerals:
            numeral = m.group(0)
            if before is None:
                where = ' '.join(context[max(0, m.start() - 55):m.end() + 25].split())
            else:
                where = before + ' $' + context.strip() + '$'
            x = value(numeral)
            if x.denominator == 1 and x <= SMALL and '.' not in numeral:
                self.small += 1
            elif x in self.values:
                self.repeats.append((numeral, where))
            elif x in self.recorded:
                self.copied.append((numeral, where))
            elif x in self.literals:
                self.parameters.append((numeral, where))
            else:
                self.unsupported.append((numeral, where))

    def counts(self):
        return (self.bound, len(self.repeats) + len(self.copied), len(self.parameters), len(self.unsupported))


# ---------------------------------------------------------------------------------------------
# 3. The versions, from the history of the repository
# ---------------------------------------------------------------------------------------------

NAMES = {1: 'audit-surfaces', 2: 'laws-instead-of-bodies', 3: 'generate-and-check',
         4: 'consent-as-a-linear-resource', 5: 'ask-only-when-it-matters', 6: 'what-an-agent-loop-costs',
         7: 'an-injection-is-a-choice', 8: 'a-crash-is-a-lost-reply', 9: 'a-merge-is-a-schedule'}

# paper, version, commit: the lines of papers/VERSIONS when this paper was written
VERSIONS = [(1, 1, '42c737d768'), (1, 2, '8dcf819c8a'), (2, 1, '1ab02196c3'), (3, 1, '168065880b'),
            (4, 1, '827566350e'), (4, 2, 'ed3cbb4dbf'), (5, 1, 'dfcd3c778d'), (6, 1, '50ad7e927e'),
            (1, 3, '3a40f86367'), (2, 2, '3a40f86367'), (3, 2, '3a40f86367'), (4, 3, '3a40f86367'),
            (5, 2, '3a40f86367'), (6, 2, '3a40f86367'), (7, 1, '411b29c05c'), (5, 3, '7962d824bd'),
            (1, 4, 'd6234cd321'), (2, 3, 'd6234cd321'), (3, 3, '7b9a09ac2b'), (4, 4, '2be96e870e'),
            (8, 1, '7e9ebf108e'), (9, 1, 'a9d28d4eb0')]


def git(*args):
    return subprocess.run(['git', '-C', REPO] + list(args), capture_output=True, text=True, check=True).stdout


def pdf_misses(paper, commit, audit):
    """The generated values that a version's source uses and that its committed PDF does not
    show.  Needs pdftotext; returns None without it."""
    text = pdf_text(subprocess.run(['git', '-C', REPO, 'show', f'{commit}:papers/{NAMES[paper]}/paper.pdf'],
                                   capture_output=True, check=True).stdout)
    if text is None:
        return None
    text = re.sub(r'\s+', '', text)
    plain = {name for name in audit.used if '\\' not in audit.macros[name]}
    return len(plain), sorted(name for name in plain if re.sub(r'\s+', '', audit.macros[name]) not in text)


def headings(pdf_text):
    """The numbered statements, tables and figures of a paper, from the text of its PDF."""
    found = set(re.findall(r'(Theorem|Lemma|Corollary|Proposition|Definition)\s+(\d+\.\d+)\s*[.(]', pdf_text))
    found |= {('Table', num) for num in re.findall(r'Table\s+(\d+)\.', pdf_text)}
    found |= {('Figure', num) for num in re.findall(r'Fig\.\s+(\d+)\.', pdf_text)}
    return found


def mentions(text):
    """The statements, tables and figures that a text refers to by number."""
    out = []
    for m in re.finditer(r'\b(Theorem|Lemma|Corollary|Proposition|Definition|Table|Figure)s?\s+'
                         r'(\d+(?:\.\d+)?(?:(?:,\s*|,?\s+and\s+)\d+(?:\.\d+)?)*)', text):
        out += [(m.group(1), num) for num in re.findall(r'\d+(?:\.\d+)?', m.group(2))]
    return out


def pdf_text(data):
    try:
        return subprocess.run(['pdftotext', '-', '-'], input=data, capture_output=True,
                              check=True).stdout.decode('utf-8', 'ignore')
    except (OSError, subprocess.CalledProcessError):
        return None


def references(paper, commit):
    """The references by number from the artifact and the record of a version into its paper,
    and those among them that have no target in the committed PDF."""
    base = f'papers/{NAMES[paper]}/'
    text = pdf_text(subprocess.run(['git', '-C', REPO, 'show', f'{commit}:{base}paper.pdf'],
                                   capture_output=True, check=True).stdout)
    targets, refs = headings(text), []
    for path in git('ls-tree', '-r', '--name-only', commit, base).split():
        if path.endswith(('.py', '.lean', 'check.txt', 'meta.yaml', 'Makefile')):
            refs += [(kind, num, path.split('/')[-1]) for kind, num in mentions(git('show', f'{commit}:{path}'))]
    return refs, [ref for ref in refs if ref[:2] not in targets]


def version(paper, commit):
    """The text of a paper at a commit, and the files of its directory that are text."""
    base = f'papers/{NAMES[paper]}/'
    files = {}
    for path in git('ls-tree', '-r', '--name-only', commit, base).split():
        if path.endswith(('.tex', '.py', '.lean', 'Makefile', '.sh', '.txt')) and 'lean-imports' not in path:
            files[path[len(base):]] = git('show', f'{commit}:{path}')
    return files['paper.tex'], files


# ---------------------------------------------------------------------------------------------
# 4. The calculus of Section 3: documents, rendering, and what a numeral denotes
# ---------------------------------------------------------------------------------------------

def shown(x, digits):
    """A number as a numeral with a given number of digits after the point, rounded half up."""
    scaled = (x * 10 ** digits + Fraction(1, 2)).__floor__()
    whole, part = divmod(scaled, 10 ** digits)
    return f'{whole:,}' + ('.' + str(part).zfill(digits) if digits else '')


def denotes(numeral):
    """The interval of the numbers that a numeral stands for: [low, high)."""
    digits = len(numeral.split('.')[1]) if '.' in numeral else 0
    half = Fraction(1, 2 * 10 ** digits)
    return value(numeral) - half, value(numeral) + half


def render(doc, record):
    """A document is a list of items: ('text', s) | ('lit', numeral) | ('bound', expr, digits)
    | ('claim', test, s), where an expression or a test is a function of the record.  Returns
    the rendered pieces with their labels, or None if a claim fails."""
    out = []
    for item in doc:
        if item[0] in ('text', 'lit'):
            out.append(('written', item[1]))
        elif item[0] == 'bound':
            out.append(('computed', shown(item[1](record), item[2])))
        elif not item[1](record):
            return None
        else:
            out.append(('checked', item[2]))
    return out


def quotient(a, b):
    """The interval of x / y for x in the interval a and y in the interval b, with b positive."""
    return a[0] / b[1], a[1] / b[0]


def main(outdir):
    rng = random.Random(2026)
    lines, nums = [], {}

    # Theorems 3.2 and 3.3 on random documents and records
    keys = ['k%d' % i for i in range(6)]
    for _ in range(3000):
        record = {k: Fraction(int(rng.random() * 10 ** 6), 10 ** int(rng.random() * 4)) for k in keys}
        other = {k: (record[k] if rng.random() < 0.5 else record[k] + 1) for k in keys}
        doc, twin = [], []
        for _ in range(8):
            r = rng.random()
            a, b = keys[int(rng.random() * 6)], keys[int(rng.random() * 6)]
            if r < 0.3:
                item = ('bound', (lambda rec, a=a: rec[a]), int(rng.random() * 3))
            elif r < 0.45:
                item = ('bound', (lambda rec, a=a, b=b: rec[a] + rec[b]), int(rng.random() * 3))
            elif r < 0.6:
                item = ('claim', (lambda rec, a=a, b=b: rec[a] <= rec[b] + 1), 'at most')
            else:
                item = ('text', 'word%d' % int(rng.random() * 9))
            doc.append(item)
            twin.append(('text', 'other') if item[0] == 'text' else item)
        out = render(doc, record)
        if out is not None:
            for item, (label, text) in zip(doc, out):
                if item[0] == 'bound':        # faithfulness: the value lies in what the numeral denotes
                    low, high = denotes(text)
                    assert label == 'computed' and low <= item[1](record) < high
                if item[0] == 'claim':
                    assert label == 'checked' and item[1](record)
            # what is written does not reach what is computed
            assert [p for p in render(twin, record) if p[0] != 'written'] == [p for p in out if p[0] != 'written']
        again = render(doc, other)
        if out is not None and again is not None:   # the record does not reach what is written
            assert [p for p in again if p[0] == 'written'] == [p for p in out if p[0] == 'written']
    lines.append('3000 random documents: every computed numeral denotes an interval that contains its value, '
                 'every claim that is rendered holds, the written parts do not change the computed parts, and '
                 'the record does not change the written parts')

    # Proposition 3.4: a quotient of rounded numbers
    worst = Fraction(0)
    for _ in range(20000):
        x, y = Fraction(100 + int(rng.random() * 9900), 100), Fraction(100 + int(rng.random() * 9900), 100)
        a, b = shown(x, 1), shown(y, 1)
        low, high = quotient(denotes(a), denotes(b))
        assert low < x / y < high
        bound = (value(a) / value(b)) * (Fraction(1, 20) / value(a) + Fraction(1, 20) / value(b)) * Fraction(11, 10)
        assert high - value(a) / value(b) <= bound and value(a) / value(b) - low <= bound
        worst = max(worst, (high - low) / (x / y))
    lines.append('20000 quotients of numbers shown with one digit: the true quotient lies in the interval '
                 'computed from the numerals, and the interval is as narrow as Proposition 3.4 says')

    # the audit of the versions
    rows, latest, shown_, missing = [], {}, 0, 0
    for paper, ver, commit in VERSIONS:
        tex, files = version(paper, commit)
        audit = Audit(tex, files)
        assert not audit.redefined
        rows.append((paper, ver, audit))
        latest[paper] = (ver, audit)
        pdf = pdf_misses(paper, commit, audit)
        assert pdf is not None, 'the check of the PDFs needs pdftotext'
        shown_, missing = shown_ + pdf[0], missing + len(pdf[1])
    assert missing == 0
    lines.append(f'the committed PDF of each of the {len(VERSIONS)} versions shows every generated value that '
                 f'its source uses: {shown_} values')
    nums.update(PdfValues=str(shown_))

    # the numbers that point the other way: from the artifact and the record into the paper
    pointing = dangling = 0
    stale = {}
    for paper, ver, commit in VERSIONS:
        refs, lost = references(paper, commit)
        pointing, dangling = pointing + len(refs), dangling + len(lost)
        if lost:
            stale[(paper, ver)] = lost
    assert set(stale) == {(1, 4), (3, 3)}
    assert {ref[:2] for ref in stale[(1, 4)]} == {('Corollary', '4.1'), ('Theorem', '4.3'), ('Theorem', '3.2')}
    assert [ref[:2] for ref in stale[(3, 3)]] == [('Figure', '2')]
    lines.append(f'{pointing} references by number from artifacts and records into their papers, in all '
                 f'versions: {dangling} have no target in the PDF of their version, '
                 + ' and '.join(f'{len(lost)} in paper {p} version {v}' for (p, v), lost in sorted(stale.items())))
    # found by reading, when the two files were corrected: references whose number now belongs
    # to another statement, which the check above cannot see.  (The numbers are those of paper
    # 1, so they are put together here and not written as references.)
    def name(kind, number):
        return kind + ' ' + number

    names = dict(re.findall(r'((?:Theorem|Proposition) \d+\.\d+) \(([A-Za-z ]+)\)', pdf_text(subprocess.run(
        ['git', '-C', REPO, 'show', 'd6234cd321:papers/audit-surfaces/paper.pdf'], capture_output=True).stdout)))
    assert names[name('Theorem', '4.2')] == 'Interface soundness' and names[name('Theorem', '5.2')] == 'Merging'
    assert names[name('Proposition', '3.3')] == 'One pass'
    assert names[name('Proposition', '4.3')] == 'Contents of the surface'
    lean = {f: git('show', 'd6234cd321:papers/audit-surfaces/artifact/' + f) for f in ('Audit.lean', 'Laws.lean')}
    wrong = (lean['Audit.lean'].count(name('Theorem', '4.2') + ': two extensions of a library merge')
             + lean['Laws.lean'].count(name('Proposition', '3.3') + ', first half: the interface surface')
             + lean['Laws.lean'].count(name('Proposition', '3.3') + ', second half: an entry of the interface surface'))
    assert wrong == 3
    nums.update(RefWrong=str(wrong))
    nums.update(RefAll=str(pointing), RefStale=str(dangling), RefStaleOne=str(len(stale[(1, 4)])),
                RefStaleOneKinds=str(len({ref[:2] for ref in stale[(1, 4)]})), RefStaleThree=str(len(stale[(3, 3)])))

    # the quantities of the latest versions that nothing supported, each checked here by hand
    HAND = {
        (1, '2,100'): ('size', lambda: 2100 / (lines_of(1, 'Audit.lean') + lines_of(1, 'Laws.lean'))),
        (2, '400'): ('size', lambda: 400 / lines_of(2, 'Laws.lean')),
        (3, '420'): ('size', lambda: 420 / lines_of(3, 'grades.py')),
        (6, '700'): ('size', lambda: 700 / lines_of(6, 'cost.py')),
        (7, '840'): ('size', lambda: 840 / lines_of(7, 'flow.py')),
        (2, '217'): ('cited', lambda: 1 if Fraction(217) in cited else 0),
        (2, '1,134'): ('cited', lambda: 1 if Fraction(1134) in cited else 0),
        (6, '1.25'): ('external', None),
        (6, '0.1'): ('external', None),
        (6, '23,000'): ('derived', lambda: 23000 / (float(value(latest[6][1].macros['exQuestion'])) / 4)),
        (6, '26'): ('derived', lambda: 26 / round((2 * (19100 + 7880) / (0.08 * 1000)) ** 0.5)),
        (6, '1.143'): ('derived', lambda: 1.143 / round(8 / 7, 3)),
        (6, '1.5'): ('derived', lambda: 1 if float(value(latest[6][1].macros['exTabPlainHundred']))
                     / float(value(latest[6][1].macros['exTabCompHundred'])) <= 1.5 else 0),
        (3, '0.05'): ('notation', lambda: 1 if 'Fraction(1, 20)' in sources_of(3) or '1, 20' in sources_of(3) else 0),
        (9, '4.36'): ('version', lambda: 1 if 'Lean 4.36' in git('show', 'a9d28d4eb0:papers/a-merge-is-a-schedule/'
                                                                'artifact/lean-imports.txt')[:40] else 0),
    }
    commits = {paper: commit for paper, ver, commit in VERSIONS}

    def lines_of(paper, name):
        return len(git('show', f'{commits[paper]}:papers/{NAMES[paper]}/artifact/{name}').splitlines())

    def sources_of(paper):
        return '\n'.join(content for path, content in version(paper, commits[paper])[1].items()
                         if path.endswith('.py'))

    cited = Audit(*version(1, '8dcf819c8a')).values        # the version of paper 1 that paper 2 cites
    found = {(paper, numeral) for paper in latest for numeral, _ in latest[paper][1].unsupported}
    assert found == set(HAND), found ^ set(HAND)
    kinds = {}
    for key, (kind, check) in HAND.items():
        kinds[kind] = kinds.get(kind, 0) + sum(1 for n, _ in latest[key[0]][1].unsupported if n == key[1])
        if check is not None:
            assert 0.97 <= check() <= 1.03, key
    lines.append('the quantities of the latest versions that nothing supports, by kind: '
                 + ', '.join(f'{kind} {n}' for kind, n in sorted(kinds.items()))
                 + '; all but the external ones are checked here')
    for kind, n in kinds.items():
        nums['Kind' + kind.capitalize()] = str(n)
    nums['KindChecked'] = str(sum(n for kind, n in kinds.items() if kind != 'external'))
    with open(f'{outdir}/unsupported.txt', 'w') as f:
        for paper in sorted(latest):
            ver, audit = latest[paper]
            f.write(f'paper {paper} version {ver} ({NAMES[paper]}): {len(audit.unsupported)} quantities that '
                    f'nothing in the artifact supports\n')
            for numeral, context in audit.unsupported:
                f.write(f'    {numeral:>12}   {context}\n')
            f.write(f'  {len(audit.repeats) + len(audit.copied)} quantities that repeat a generated value or '
                    f'the recorded output\n')
            for numeral, context in audit.repeats + audit.copied:
                f.write(f'    {numeral:>12}   {context}\n')
            f.write(f'  {len(audit.parameters)} quantities that repeat a literal of the source\n')
            for numeral, context in audit.parameters:
                f.write(f'    {numeral:>12}   {context}\n')
    # an excerpt of the report, for Figure 3 of the paper
    six_ = latest[6][1]
    with open(f'{outdir}/excerpt.tex', 'w') as f:
        f.write('% written by evidence.py; do not edit\n\\begin{verbatim}\n')
        for title, items in ((f'{len(six_.unsupported)} quantities that nothing in the artifact supports',
                              six_.unsupported[2:5]),
                             (f'{len(six_.repeats) + len(six_.copied)} quantities that repeat a generated value',
                              six_.repeats[:2]),
                             (f'{len(six_.parameters)} quantities that repeat a literal of the source',
                              six_.parameters[2:5])):
            f.write(title + '\n')
            for numeral, context in items:
                f.write(f'{numeral:>9}   {context}'[:84] + '\n')
        f.write('\\end{verbatim}\n')

    table = []
    for paper, ver, audit in rows:
        b, rep_, par, uns = audit.counts()
        table.append(f'{paper}v{ver}: {b} bound, {rep_} repeat a generated value, {par} repeat the source, '
                     f'{uns} unsupported')
    lines.append('the quantities of every version: ' + '; '.join(table))
    for paper in sorted(latest):
        ver, audit = latest[paper]
        b, rep_, par, uns = audit.counts()
        total = b + rep_ + par + uns
        tag = 'abcdefghi'[paper - 1]
        nums.update({'Bound' + tag: str(b), 'Repeat' + tag: str(rep_), 'Param' + tag: str(par),
                     'Unsup' + tag: str(uns), 'Total' + tag: str(total), 'Version' + tag: str(ver),
                     'Share' + tag: f'{100 * b / total:.0f}' if total else '--',
                     'Words' + tag: str(audit.words + audit.parts), 'Formal' + tag: str(audit.formal),
                     'Small' + tag: str(audit.small)})
    first = {}
    for paper, ver, audit in rows:
        first.setdefault(paper, audit)
    for paper in sorted(first):
        b, rep_, par, uns = first[paper].counts()
        total = b + rep_ + par + uns
        nums['First' + 'abcdefghi'[paper - 1]] = f'{100 * b / total:.0f}' if total else '--'
    all_b = sum(a.counts()[0] for _, a in latest.values())
    all_t = sum(sum(a.counts()) for _, a in latest.values())
    nums.update(AllBound=f'{all_b:,}', AllTotal=f'{all_t:,}', AllShare=f'{100 * all_b / all_t:.0f}',
                AllRepeat=str(sum(a.counts()[1] for _, a in latest.values())),
                AllParam=str(sum(a.counts()[2] for _, a in latest.values())),
                AllUnsup=str(sum(a.counts()[3] for _, a in latest.values())),
                Versions=str(len(VERSIONS)), Papers=str(len(latest)))

    # the share of bound quantities in every version, and the checks of the unsupported ones
    for paper, ver, audit in rows:
        b, total = audit.counts()[0], sum(audit.counts())
        nums[f'Hist{"abcdefghi"[paper - 1]}{"abcd"[ver - 1]}'] = f'{100 * b / total:.0f}' if total else '--'
    nums.update(HandSizeA=f'{lines_of(1, "Audit.lean") + lines_of(1, "Laws.lean"):,}',
                HandSizeB=str(lines_of(2, 'Laws.lean')), HandSizeC=str(lines_of(3, 'grades.py')),
                HandSizeF=str(lines_of(6, 'cost.py')), HandSizeG=str(lines_of(7, 'flow.py')),
                HandQuestion=latest[6][1].macros['exQuestion'],
                HandFormula=f'{(2 * (19100 + 7880) / (0.08 * 1000)) ** 0.5:.2f}',
                HandFraction=f'{8 / 7:.4f}')
    for (paper, numeral), (kind, _) in HAND.items():
        nums['Hand' + kind.capitalize() + 'abcdefghi'[paper - 1]
             + re.sub(r'[^A-Za-z]', '', {'217': 'x', '1,134': 'y', '23,000': 'p', '26': 'q', '1.143': 'r',
                                         '1.5': 's', '1.25': 'u', '0.1': 'v'}.get(numeral, ''))] = numeral
    one = first[1]
    hand = one.repeats + one.copied + one.parameters + one.unsupported
    nums.update(OneSame=str(sum(value(numeral) in cited for numeral, _ in hand)))
    nums.update(OneHand=str(sum(one.counts()[1:])), OneCopied=str(len(one.copied)),
                OneDerived=str(len(one.unsupported)), OneSource=str(len(one.parameters)),
                AllWords=str(sum(a.words + a.parts for _, a in latest.values())),
                AllSmall=f'{sum(a.small for _, a in latest.values()):,}',
                AllFormal=f'{sum(a.formal for _, a in latest.values()):,}',
                SmallLimit=str(SMALL), Documents='3,000', Quotients='20,000')

    # the examples of Sections 2 and 3, from the audited papers
    four, six, nine = latest[4][1], latest[6][1], latest[9][1]
    assert {n for n, _ in four.repeats} == {'3,000'}
    true_size = lines_of(1, 'Audit.lean') + lines_of(1, 'Laws.lean')
    plain, comp = (float(value(six.macros[k])) for k in ('exTabPlainHundred', 'exTabCompHundred'))
    nums.update(EgTwice='3,000', EgTwiceCount=str(len(four.repeats)), EgBound=four.macros['exLatePercent'],
                EgSize='2,100', EgSizeTrue=f'{true_size:,}', EgDerived='1.5', EgDerivedTrue=f'{plain / comp:.2f}',
                EgPlain=six.macros['exTabPlainHundred'], EgComp=six.macros['exTabCompHundred'],
                EgCited='217', EgCitedVersion='2')
    # a quotient that a reader can check from the numerals, and one that a reader cannot
    p, p2 = nine.macros['exFleetP'], nine.macros['exFleetMutual']
    low, high = quotient(denotes(p), denotes(p2))
    assert denotes(nine.macros['exFleetRatio'])[0] <= low and high <= denotes(nine.macros['exFleetRatio'])[1]
    nums.update(EgP=p, EgPTwo=p2, EgRatio=nine.macros['exFleetRatio'], EgLow=shown(low, 2), EgHigh=shown(high, 2))
    a, b = four.macros['exLatePercent'], four.macros['exStoppedPercent']
    late, stopped, runs = (value(four.macros[k]) for k in ('exLate', 'exStopped', 'exRejectedRuns'))
    ratio = shown((late / stopped) / (stopped / runs), 2)
    low, high = quotient(denotes(a), denotes(b))
    assert not (denotes(ratio)[0] <= low and high <= denotes(ratio)[1]) and low < value(ratio) < high
    nums.update(EgA=a, EgB=b, EgQuot=ratio, EgQLow=shown(low, 2), EgQHigh=shown(high, 2))

    # what the paper says in words about these numbers
    early = [first[p].counts()[0] for p in sorted(first) if p <= 5]
    claims = {
        'three-quarters': 4 * all_b > 3 * all_t,
        'early-none': all(b == 0 for b in early),
        'sizes-most': kinds['size'] == max(kinds.values()),
        'checked-right': True,              # the assertions above
        'pdf-agree': missing == 0,
        'copied-most': 10 * len(one.copied) > 9 * sum(one.counts()[1:]),
        'six-least': min((latest[p][1].counts()[0] / sum(latest[p][1].counts()), p)
                         for p in latest if latest[p][1].counts()[0])[1] == 6,
    }
    claims['stale-rewritten'] = set(stale) == {(1, 4), (3, 3)}     # the two papers that were rewritten
    seeds = os.path.join(HERE, 'expected', 'seeds.tex')
    if os.path.exists(seeds):               # the results of seeds.py, which takes minutes
        other = generated('\\input{seeds.tex}', {'seeds.tex': open(seeds).read()})
        claims['one-stops'] = other['exSeedFailed'] == '1' and other['exSeedPassh'] == '2'
        claims['closed-none'] = other['exSeedChangef'] == '0'
        claims['coarse-no-better'] = abs(int(other['exSeedCoarsePercent']) - int(other['exSeedFinePercent'])) <= 5
    assert all(claims.values()), claims

    # this paper, by its own standard: every quantity is bound, and every claim is checked
    path = os.path.join(HERE, '..', 'paper.tex')
    if os.path.exists(path):
        tex = re.sub(r'\\begin\{verbatim\}.*?\\end\{verbatim\}', '', open(path).read(), flags=re.S)
        files = {'artifact/expected/numbers.tex': '\n'.join(
            f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}' for name in nums)}
        if os.path.exists(seeds):
            files['artifact/expected/seeds.tex'] = open(seeds).read()
        own = Audit(tex, files)
        assert not (own.repeats or own.copied or own.parameters or own.unsupported), \
            (own.repeats, own.copied, own.parameters, own.unsupported)
        assert not own.redefined
        used = set(re.findall(r'\\claim\{([a-z-]+)\}', tex))
        assert used == set(claims), used ^ set(claims)
        pdf = os.path.join(HERE, '..', 'paper.pdf')
        if os.path.exists(pdf):             # the references of this artifact into this paper
            targets = headings(pdf_text(open(pdf, 'rb').read()))
            for name in ('evidence.py', 'seeds.py', 'Makefile', '../meta.yaml'):
                lost = [ref for ref in mentions(open(os.path.join(HERE, name)).read()) if ref not in targets]
                assert not lost, (name, lost)
        lines.append(f'this paper: {own.bound} quantities, all bound; {len(claims)} claims in words, all checked')
        nums.update(OwnClaims=str(len(claims)))

    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by evidence.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
