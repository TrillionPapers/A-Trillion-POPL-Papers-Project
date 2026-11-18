#!/usr/bin/env python3
"""Runs the scripts of the earlier papers again with other random seeds, for Section 6 of "A
Number Is a Claim".  For every script and seed it reports whether the script still passes all
its own tests and assertions, and how many of the generated values change.

`python3 seeds.py out` writes out/seeds.txt and out/seeds.tex.  It needs git with the history
of the repository and takes a few minutes.  It is not part of `make check`."""
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, '..', '..', '..'))

# paper, directory, script, the commit of its latest recorded version
SCRIPTS = [(3, 'generate-and-check', 'grades.py', '7b9a09ac2b'),
           (4, 'consent-as-a-linear-resource', 'consent.py', '2be96e870e'),
           (6, 'what-an-agent-loop-costs', 'cost.py', '3a40f86367'),
           (7, 'an-injection-is-a-choice', 'flow.py', '411b29c05c'),
           (8, 'a-crash-is-a-lost-reply', 'journal.py', '7e9ebf108e'),
           (9, 'a-merge-is-a-schedule', 'merge.py', 'a9d28d4eb0')]
SEEDS = (1, 2, 3)


def git(*args):
    return subprocess.run(['git', '-C', REPO] + list(args), capture_output=True, text=True, check=True).stdout


def values(text):
    return dict(re.findall(r'\\newcommand\{\\([A-Za-z]+)\}\{(.*)\}', text))


def main(outdir):
    lines, nums = [], {}
    passed = failed = 0
    coarse = [0, 0]             # values with at most two significant digits: all, and unchanged by any seed
    fine = [0, 0]               # values with more
    for paper, name, script, commit in SCRIPTS:
        base = f'{commit}:papers/{name}/artifact/'
        source = git('show', base + script)
        recorded = values(git('show', base + 'expected/numbers.tex'))
        seeds = re.findall(r'random\.Random\((\d+)\)', source)
        assert seeds.count('2026') == 1, (paper, seeds)
        changed, outcome, moved = [], [], set()
        for seed in SEEDS:
            with tempfile.TemporaryDirectory() as tmp:
                with open(os.path.join(tmp, script), 'w') as f:
                    f.write(source.replace('random.Random(2026)', f'random.Random({seed})'))
                if paper == 9:
                    with open(os.path.join(tmp, 'lean-imports.txt'), 'w') as f:
                        f.write(git('show', base + 'lean-imports.txt'))
                os.mkdir(os.path.join(tmp, 'out'))
                run = subprocess.run([sys.executable, script, 'out'], cwd=tmp, capture_output=True, text=True)
                if run.returncode == 0:
                    fresh = values(open(os.path.join(tmp, 'out', 'numbers.tex')).read())
                    assert set(fresh) == set(recorded)
                    changed.append(sum(fresh[k] != recorded[k] for k in recorded))
                    moved |= {k for k in recorded if fresh[k] != recorded[k]}
                    outcome.append(f'passes, {changed[-1]} values change')
                    passed += 1
                else:
                    where = [l.strip() for l in run.stderr.splitlines() if l.strip().startswith('assert')]
                    outcome.append('fails at: ' + (where[-1] if where else run.stderr.strip().splitlines()[-1]))
                    failed += 1
        lines.append(f'paper {paper}, {script}, {len(recorded)} generated values: '
                     + '; '.join(f'seed {s} {o}' for s, o in zip(SEEDS, outcome)))
        for key, text in recorded.items():
            if re.fullmatch(r'[\d,.]+', text) and changed:
                digits = len(re.sub(r'[,.]', '', text).lstrip('0')) or 1
                group = coarse if digits <= 2 else fine
                group[0] += 1
                group[1] += key not in moved
        tag = 'abcdefghi'[paper - 1]
        nums['SeedValues' + tag] = str(len(recorded))
        nums['SeedPass' + tag] = str(len(changed))
        nums['SeedChange' + tag] = str(max(changed)) if changed else '--'
        nums['SeedKeep' + tag] = str(len(recorded) - max(changed)) if changed else '--'
    nums.update(SeedRuns=str(passed + failed), SeedPassed=str(passed), SeedFailed=str(failed),
                SeedScripts=str(len(SCRIPTS)), SeedCount=str(len(SEEDS)),
                SeedCoarse=str(coarse[0]), SeedCoarseKept=str(coarse[1]),
                SeedCoarsePercent=f'{100 * coarse[1] / coarse[0]:.0f}',
                SeedFine=str(fine[0]), SeedFineKept=str(fine[1]), SeedFinePercent=f'{100 * fine[1] / fine[0]:.0f}')
    lines.append(f'numerals with at most two significant digits: {coarse[1]} of {coarse[0]} are the same under '
                 f'every seed that passes; with more digits: {fine[1]} of {fine[0]}')
    with open(f'{outdir}/seeds.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/seeds.tex', 'w') as f:
        f.write('% written by seeds.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
