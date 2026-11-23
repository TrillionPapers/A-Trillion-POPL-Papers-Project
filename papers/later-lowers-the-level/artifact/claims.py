#!/usr/bin/env python3
"""Type-checks the three Agda files and records what they establish.

usage: claims.py OUT_DIR

Every claim of the paper that a machine checked is a definition in one of the files: that
Agda accepts the definition, with --safe and --without-K, is the claim.  The script runs
Agda, looks up every definition, compares the names with the \\claim marks of the paper, and
writes OUT_DIR/check.txt, OUT_DIR/numbers.tex and OUT_DIR/version.tex.
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = ['Diagonal.agda', 'Collapse.agda', 'Stratified.agda']

# name in the paper, file, definition, what the definition says
CLAIMS = [
    ('lowering', 'Diagonal.agda', 'later',
     'the later of a presheaf over the level above l is a presheaf over l'),
    ('usual-later', 'Diagonal.agda', 'later0',
     'the later that keeps the level is the lowering one after raising the level'),
    ('fixed-points', 'Diagonal.agda', 'fix',
     'every map from the later of a presheaf to the presheaf has a fixed point'),
    ('products', 'Diagonal.agda', 'Prod',
     'the dependent product of presheaves over l is a presheaf over l'),
    ('universe', 'Diagonal.agda', 'Univ',
     'the universe of presheaves over l is a presheaf over the level above l'),
    ('later-universe', 'Diagonal.agda', 'laterUniv',
     'the later of the universe over l is a presheaf over l'),
    ('codes', 'Diagonal.agda', 'laterCode',
     'later on codes maps the later of the universe above l to the universe over l'),
    ('decoding', 'Diagonal.agda', 'shift-top',
     'decoding commutes with later on codes'),
    ('worlds', 'Diagonal.agda', 'WorldF',
     'the right-hand side of the equation for worlds maps presheaves over l to presheaves over l'),
    ('paradox', 'Collapse.agda', 'paradox',
     'a universe closed under products that is a retract of one of its types has every type inhabited'),
    ('clocks', 'Collapse.agda', 'collapse',
     'a level-keeping operation from large codes to small codes with retractions collapses the small universe'),
    ('stages', 'Stratified.agda', 'World',
     'worlds of depth n live at level n, predicates of depth n one level above'),
    ('guarded-quantifier', 'Stratified.agda', 'allLater',
     'the quantifier over the predicates of the stage before keeps the level of its stage'),
    ('plain-quantifier', 'Stratified.agda', 'allNow',
     'the quantifier over the predicates of the same stage is typed one level higher'),
    ('holds', 'Stratified.agda', 'holds',
     'the predicate that a location holds a given predicate keeps the level of its stage'),
]

# Files that Agda must reject, with a word that its error message must contain.
REJECTED = [
    ('keep-rejected', 'RejectedKeep.agda', 'WorldKeep', 'Unequal',
     'with the later that keeps the level, the right-hand side of the equation for worlds '
     'is not a presheaf over l'),
    ('now-rejected', 'RejectedNow.agda', 'allSame', 'Unequal',
     'the quantifier over the predicates of the same stage is not at the level of the stage'),
]


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    version = subprocess.run(['agda', '--version'], capture_output=True, text=True).stdout.split()[2]
    text = {}
    for name in FILES:
        path = os.path.join(HERE, name)
        text[name] = open(path, encoding='utf-8').read()
        for word in ('postulate', 'TERMINATING', 'type-in-type', 'NO_POSITIVITY', 'NO_UNIVERSE'):
            assert word not in text[name], '%s mentions %s' % (name, word)
        assert '--safe' in text[name].splitlines()[0], name
        done = subprocess.run(['agda', '--safe', '--without-K', name], cwd=HERE,
                              capture_output=True, text=True)
        if done.returncode != 0:
            sys.stderr.write(done.stdout + done.stderr)
            sys.exit('Agda rejects %s' % name)
    lines = []
    for claim, name, definition, says in CLAIMS:
        found = re.search(r'^\s*%s\s+:' % re.escape(definition), text[name], re.M)
        assert found, 'no definition %s in %s' % (definition, name)
        lines.append('%s: %s, definition %s: %s' % (claim, name, definition, says))
    for claim, name, definition, word, says in REJECTED:
        source = open(os.path.join(HERE, name), encoding='utf-8').read()
        assert re.search(r'^\s*%s\s+:' % re.escape(definition), source, re.M), name
        done = subprocess.run(['agda', '--safe', '--without-K', name], cwd=HERE,
                              capture_output=True, text=True)
        assert done.returncode != 0, 'Agda accepts %s' % name
        assert word in done.stdout + done.stderr, 'unexpected error for %s' % name
        lines.append('%s: %s, definition %s, rejected by Agda: %s' % (claim, name, definition, says))
    paper = os.path.join(HERE, '..', 'paper.tex')
    if os.path.exists(paper):
        marked = set(re.findall(r'\\claim\{([a-z0-9-]+)\}', open(paper, encoding='utf-8').read()))
        named = {row[0] for row in CLAIMS + REJECTED}
        assert marked == named, 'claims of the paper and of the script differ: %s' % sorted(marked ^ named)
    with open(os.path.join(out, 'check.txt'), 'w') as handle:
        handle.write('\n'.join(lines) + '\n')
    count = {name: len(text[name].splitlines()) for name in FILES}
    with open(os.path.join(out, 'numbers.tex'), 'w') as handle:
        handle.write('%% written by claims.py\n')
        handle.write('\\newcommand{\\LinesDiagonal}{%d}\n' % count['Diagonal.agda'])
        handle.write('\\newcommand{\\LinesCollapse}{%d}\n' % count['Collapse.agda'])
        handle.write('\\newcommand{\\LinesStratified}{%d}\n' % count['Stratified.agda'])
        handle.write('\\newcommand{\\LinesAll}{%d}\n' % sum(count.values()))
        handle.write('\\newcommand{\\CheckedClaims}{%d}\n' % (len(CLAIMS) + len(REJECTED)))
    with open(os.path.join(out, 'version.tex'), 'w') as handle:
        handle.write('\\newcommand{\\AgdaVersion}{%s}\n' % version)
    print('Agda %s accepts %s and rejects %s; %d claims'
          % (version, ', '.join(FILES), ', '.join(row[1] for row in REJECTED),
             len(CLAIMS) + len(REJECTED)))


if __name__ == '__main__':
    main()
