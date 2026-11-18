#!/usr/bin/env python3
"""Tests the claims of "Turning Errors into Abstentions" on small programs, with exact numbers.

The file has five parts.

1. Programs, oracles, and checkers over the values 0..3.
2. The grades of Figure 1: for a program, the set of right results, a bound on the probability
   of a wrong result, a bound on the probability of a failure, and a bound on the expected
   number of calls.
3. The game: the exact supremum of each of these three quantities over all environments that
   respect the failure rates.  An environment may adapt to everything it has seen, so the
   supremum is the value of a game, which backward induction computes.
4. Random programs and the programs of the paper.
5. The tests.  `python3 grades.py out` writes out/check.txt and out/numbers.tex.

A test is not a proof.  The proofs are in the paper.
"""
import random
import sys
from fractions import Fraction as Q
from itertools import count
from math import comb

V = range(4)
BOT = None
ALL = frozenset(V)

# an oracle has a failure rate and, for each input, the set of right answers
ORACLES = {
    'succ': (Q(1, 4), lambda v: {(v + 1) % 4}),
    'flip': (Q(1, 3), lambda v: {3 - v}),
    'below': (Q(1, 5), lambda v: {u for u in V if u <= v}),
    'even': (Q(1, 2), lambda v: {0, 2}),
}
# a judge accepts a value outside its set with probability at most alpha, and rejects a value
# inside it with probability at most beta
JUDGES = {
    'small': (Q(1, 10), Q(1, 20), frozenset({0, 1})),
    'nonzero': (Q(1, 5), Q(0), frozenset({1, 2, 3})),
    'two': (Q(1, 2), Q(1, 4), frozenset({2})),
}
FUN = {'inc': lambda v: (v + 1) % 4, 'half': lambda v: v // 2, 'id': lambda v: v}


# ---------------------------------------------------------------------------------------------
# 1. Programs.  Arguments: ('c', n) | ('v', x) | ('f', name, x).  Tests: ('le', a, b).
#    Expressions: ('ret', a) | ('call', o, a) | ('let', x, e1, e2) | ('if', test, e1, e2)
#    | ('check', set, e) | ('judge', j, e) | ('or', e1, e2) | ('vote', k, e)
# ---------------------------------------------------------------------------------------------

def aval(a, env):
    if a[0] == 'c':
        return a[1]
    if a[0] == 'v':
        return env[a[1]]
    return FUN[a[1]](env[a[2]])


def holds(test, env):
    return aval(test[1], env) <= aval(test[2], env)


def retry(n, e):
    return e if n == 1 else ('or', e, retry(n - 1, e))


# ---------------------------------------------------------------------------------------------
# 2. Grades
# ---------------------------------------------------------------------------------------------

BROKEN = None       # the name of a rule that is deliberately broken, for the mutation test
UNION = False       # the rules of the first version of the paper, which add where these multiply


def oplus(a, b):
    return min(Q(1), a + b) if UNION else a + b - a * b


def tail(k, m, p):
    """The probability that a binomial variable with k trials and rate p is at least m."""
    return sum(comb(k, i) * p ** i * (1 - p) ** (k - i) for i in range(m, k + 1))


def ty(e, env):
    """The set of right results, and the bounds on wrong results, failures and calls."""
    k = e[0]
    if k == 'ret':
        return frozenset({aval(e[1], env)}), Q(0), Q(0), Q(0)
    if k == 'call':
        d, right = ORACLES[e[1]]
        if BROKEN == 'oracle':
            d = d / 2
        return frozenset(right(aval(e[2], env))), d, d, Q(1)
    if k == 'let':
        R1, e1, g1, c1 = ty(e[2], env)
        parts = {v: ty(e[3], {**env, e[1]: v}) for v in V}
        R = frozenset().union(*[parts[v][0] for v in R1])
        e2 = max([parts[v][1] for v in R1], default=Q(0))
        g2 = max([parts[v][2] for v in R1], default=Q(0))
        # a wrong value of x also reaches e2, and it may cost more calls than any right one
        c2 = max(parts[v][3] for v in (R1 if BROKEN == 'cost-let' and R1 else V))
        if not R1:
            g1 = Q(1)
        eps = max(e1, e2) if BROKEN == 'let-eps' else oplus(e1, e2)
        gam = max(g1, g2) if BROKEN == 'let-gam' else oplus(g1, g2)
        return R, eps, gam, c1 + c2
    if k == 'if':
        return ty(e[2] if holds(e[1], env) else e[3], env)
    if k == 'check':
        R, eps, gam, c = ty(e[2], env)
        complete = R <= e[1] or BROKEN == 'check-complete'
        return e[1], Q(0), gam if complete else Q(1), c
    if k == 'judge':
        a, b, p = JUDGES[e[1]]
        R, eps, gam, c = ty(e[2], env)
        eps2 = eps * a if R <= p or BROKEN == 'judge-eps' else a
        gam2 = gam if BROKEN == 'judge-gam' else oplus(gam, b)
        return p, eps2, gam2 if R <= p else Q(1), c + 1
    if k == 'or':
        R1, e1, g1, c1 = ty(e[1], env)
        R2, e2, g2, c2 = ty(e[2], env)
        if UNION:
            eps, gam = e1 + g1 * e2, e1 + g1 * g2
        else:
            eps, gam = e1 + (g1 - e1) * e2, e1 + (g1 - e1) * g2
        if BROKEN == 'or-eps':
            eps = g1 * e2
        if BROKEN == 'or-gam':
            gam = g1 * g2
        return R1 | R2, eps, gam, c1 + (e1 if BROKEN == 'cost-or' else g1) * c2
    if k == 'vote':
        n = e[1]
        R, eps, gam, c = ty(e[2], env)
        eps2 = tail(n, n // 2 + (2 if BROKEN == 'vote-eps' else 1), eps)
        functional = len(R) == 1 or BROKEN == 'vote-gam'
        return R, eps2, tail(n, (n + 1) // 2, gam) if functional else Q(1), n * c
    raise ValueError(k)


# ---------------------------------------------------------------------------------------------
# 3. The game
# ---------------------------------------------------------------------------------------------

def majority(outcomes):
    for r in set(outcomes):
        if r is not BOT and 2 * outcomes.count(r) > len(outcomes):
            return r
    return BOT


def game(e, env, k, calls):
    """The supremum, over the environments within the rates, of the expectation of k applied
    to the outcome, plus the number of calls if calls is set."""
    kind = e[0]
    one = 1 if calls else 0
    if kind == 'ret':
        return k(aval(e[1], env))
    if kind == 'call':
        d, right = ORACLES[e[1]]
        rs = right(aval(e[2], env))
        good = max(k(u) for u in rs)
        wrong = [k(u) for u in V if u not in rs]
        return one + good + (d * max(Q(0), max(wrong) - good) if wrong else 0)
    if kind == 'let':
        return game(e[2], env, lambda r: k(BOT) if r is BOT
                    else game(e[3], {**env, e[1]: r}, k, calls), calls)
    if kind == 'if':
        return game(e[2] if holds(e[1], env) else e[3], env, k, calls)
    if kind == 'check':
        return game(e[2], env, lambda r: k(r) if r is not BOT and r in e[1] else k(BOT), calls)
    if kind == 'judge':
        a, b, p = JUDGES[e[1]]

        def after(r):
            if r is BOT:
                return k(BOT)
            low, high = (1 - b, Q(1)) if r in p else (Q(0), a)   # the chance of acceptance
            return one + max(x * k(r) + (1 - x) * k(BOT) for x in (low, high))
        return game(e[2], env, after, calls)
    if kind == 'or':
        return game(e[1], env, lambda r: game(e[2], env, k, calls) if r is BOT else k(r), calls)
    if kind == 'vote':
        def runs(seen):
            if len(seen) == e[1]:
                return k(majority(seen))
            return game(e[2], env, lambda r: runs(seen + (r,)), calls)
        return runs(())
    raise ValueError(k)


def exact(e):
    """The grades of a closed program and the three values of its game."""
    R, eps, gam, c = ty(e, {})
    bad = game(e, {}, lambda r: Q(int(r is not BOT and r not in R)), False)
    fail = game(e, {}, lambda r: Q(int(r is BOT or r not in R)), False)
    cost = game(e, {}, lambda r: Q(0), True)
    return (eps, gam, c), (bad, fail, cost)


# ---------------------------------------------------------------------------------------------
# 4. Random programs
# ---------------------------------------------------------------------------------------------

class Gen:
    def __init__(self, rng):
        self.rng, self.names = rng, count()

    def below(self, n):
        return int(self.rng.random() * n)

    def one(self, xs):
        return xs[self.below(len(xs))]

    def arg(self, scope):
        if scope and self.rng.random() < 0.7:
            x = self.one(scope)
            return ('v', x) if self.rng.random() < 0.7 else ('f', self.one(sorted(FUN)), x)
        return ('c', self.below(len(V)))

    def subset(self):
        return frozenset(v for v in V if self.rng.random() < 0.6)

    def expr(self, depth, scope):
        r = self.rng.random()
        if depth == 0 or r < 0.2:
            if self.rng.random() < 0.3:
                return ('ret', self.arg(scope))
            return ('call', self.one(sorted(ORACLES)), self.arg(scope))
        if r < 0.45:
            x = 'x%d' % next(self.names)
            return ('let', x, self.expr(depth - 1, scope), self.expr(depth - 1, scope + [x]))
        if r < 0.55:
            return ('if', ('le', self.arg(scope), self.arg(scope)),
                    self.expr(depth - 1, scope), self.expr(depth - 1, scope))
        if r < 0.70:
            inner = self.expr(depth - 1, scope)
            if self.rng.random() < 0.5:
                # a checker that accepts every right result, for some values of the variables
                return ('check', ty(inner, {x: self.below(len(V)) for x in scope})[0] | self.subset(), inner)
            return ('check', self.subset(), inner)
        if r < 0.80:
            return ('judge', self.one(sorted(JUDGES)), self.expr(depth - 1, scope))
        if r < 0.92:
            return ('or', self.expr(depth - 1, scope), self.expr(depth - 1, scope))
        return ('vote', 2 + self.below(2), self.expr(min(depth - 1, 1), scope))


def size(e):
    """A bound on the number of calls, to keep the game small."""
    k = e[0]
    if k == 'ret':
        return 0
    if k == 'call':
        return 1
    if k in ('let', 'or'):
        return size(e[-2]) + size(e[-1])
    if k == 'if':
        return max(size(e[2]), size(e[3]))
    if k == 'vote':
        return e[1] * size(e[2])
    return size(e[2]) + (1 if k == 'judge' else 0)


def programs(rng, wanted):
    gen, out = Gen(rng), []
    while len(out) < wanted:
        e = gen.expr(3, [])
        if 1 <= size(e) <= 7:
            out.append(e)
    return out


# ---------------------------------------------------------------------------------------------
# 5. The tests
# ---------------------------------------------------------------------------------------------

RULES = ('oracle', 'let-eps', 'let-gam', 'check-complete', 'judge-eps', 'judge-gam', 'or-eps',
         'or-gam', 'vote-eps', 'vote-gam', 'cost-let', 'cost-or')


def sound(e):
    grades, values = exact(e)
    return all(v <= g for g, v in zip(grades, values))


def caught(rule, progs):
    """The number of programs tried until one shows that the broken rule is unsound."""
    global BROKEN
    BROKEN = rule
    try:
        for i, e in enumerate(progs):
            if not sound(e):
                return i + 1
        return None
    finally:
        BROKEN = None


def pct(a, b):
    return f'{100 * a / b:.0f}'


def dec(x, digits=3):
    return f'{float(x):.{digits}f}'


def main(outdir):
    global UNION
    rng = random.Random(2026)
    lines, nums = [], {}
    progs = programs(rng, 3000)

    # Theorem 5.2 and Proposition 5.3: the grades bound the values of the game
    tight = [0, 0, 0]
    for e in progs:
        grades, values = exact(e)
        assert all(v <= g for g, v in zip(grades, values)), e
        for i in range(3):
            tight[i] += grades[i] == values[i]
    lines.append(f'Theorem 5.2 and Proposition 5.3: 3000 random programs, every grade bounds the '
                 f'exact value; the bounds on wrong results, failures and calls are exact for '
                 f'{tight[0]}, {tight[1]} and {tight[2]} programs')
    nums['Programs'] = '3,000'
    nums['TightBad'], nums['TightFail'], nums['TightCost'] = (pct(t, 3000) for t in tight)

    # the rules of the first version of the paper are sound and less often exact
    UNION = True
    loose = [0, 0]
    for e in progs:
        grades, values = exact(e)
        assert all(v <= g for g, v in zip(grades, values)), e
        for i in range(2):
            loose[i] += grades[i] == values[i]
    UNION = False
    lines.append(f'with sums in place of products: still sound, exact for {loose[0]} and {loose[1]} programs')
    nums['UnionBad'], nums['UnionFail'] = pct(loose[0], 3000), pct(loose[1], 3000)

    # broken rules
    tries = {rule: caught(rule, progs) for rule in RULES}
    assert all(tries.values()), tries
    lines.append(f'{len(RULES)} broken rules, each refuted by a random program: '
                 + ', '.join(f'{rule} {n}' for rule, n in tries.items()))
    nums['Rules'], nums['Slowest'] = str(len(RULES)), str(max(tries.values()))

    # the loop: no wrong result, failures decay geometrically, the calls are a geometric sum
    cases = 0
    for o in ('succ', 'flip', 'even'):
        d, right = ORACLES[o]
        for n in range(1, 7):
            e = retry(n, ('check', frozenset(right(1)), ('call', o, ('c', 1))))
            grades, values = exact(e)
            assert grades == values == (Q(0), d ** n, sum(d ** i for i in range(n)))
            cases += 1
    # the loop with a judge in place of the checker
    for o, j, v in (('succ', 'two', 1), ('flip', 'two', 1), ('flip', 'nonzero', 0), ('below', 'small', 1)):
        d, right = ORACLES[o]
        a, b, p = JUDGES[j]
        assert right(v) <= p
        r = d * (1 - a) + (1 - d) * b
        for n in range(1, 7):
            e = retry(n, ('judge', j, ('call', o, ('c', v))))
            grades, values = exact(e)
            eps = d * a * sum(r ** i for i in range(n))
            assert grades[:2] == values[:2] == (eps, eps + r ** n), (o, j, n)
            cases += 1
    # votes
    for o in ('succ', 'flip'):
        d, right = ORACLES[o]
        for n in range(1, 6):
            e = ('vote', n, ('call', o, ('c', 2)))
            grades, values = exact(e)
            assert grades == values == (tail(n, n // 2 + 1, d), tail(n, (n + 1) // 2, d), Q(n))
            cases += 1
    # two unchecked calls in a row, where a wrong first answer shows in the result
    for o1, o2 in (('succ', 'flip'), ('flip', 'succ'), ('succ', 'succ')):
        d1, d2 = ORACLES[o1][0], ORACLES[o2][0]
        e = ('let', 'x', ('call', o1, ('c', 0)), ('call', o2, ('v', 'x')))
        grades, values = exact(e)
        assert grades[:2] == values[:2] == (d1 + d2 - d1 * d2,) * 2
        cases += 1
    lines.append(f'closed forms of Section 6: {cases} programs whose grades equal the exact values')
    nums['Cases'] = str(cases)

    # two numbers cannot be exact: the bound of a fallback depends on more than the two grades
    first = ('let', 'x', ('check', frozenset({1}), ('call', 'succ', ('c', 0))), ('call', 'flip', ('v', 'x')))
    e = ('or', first, ('call', 'even', ('c', 0)))
    grades, values = exact(e)
    assert values[0] < grades[0]
    lines.append(f'the fallback of Section 5.3: bound {grades[0]} on wrong results, exact value {values[0]}')
    nums['GapBound'], nums['GapExact'] = str(grades[0]), str(values[0])

    # a deterministic oracle is outside the class: it repeats its first answer, the loop gains
    # nothing from retries, and the grade of the loop does not apply
    d = Q(1, 4)
    for n in range(1, 6):
        abstain = d * 1 + (1 - d) * 0      # all n attempts see the first answer
        assert abstain == d and (n == 1 or d ** n < abstain)

    # the numbers of the examples
    d, a = Q(4, 5), Q(1, 20)                      # a weak generator and tests that pass 5% of wrong patches
    r = d * (1 - a)
    limit = d * a / (d * a + (1 - d))
    nums['PatchOne'] = dec(100 * d * a, 1)
    nums['PatchFive'] = dec(100 * d * a * sum(r ** i for i in range(5)), 1)
    nums['PatchLimit'] = dec(100 * limit, 1)
    nums['PatchCalls'] = dec(1 / (1 - r), 1)
    for n, name in ((1, 'One'), (3, 'Three'), (5, 'Five'), (11, 'Eleven'), (25, 'TwentyFive')):
        nums['Vote' + name] = dec(tail(n, n // 2 + 1, Q(3, 10)))
        nums['VoteBad' + name] = dec(tail(n, n // 2 + 1, Q(3, 5)))
    nums['LoopTen'] = dec(100 * Q(9, 10) ** 10, 1)
    nums['LoopCalls'] = dec(sum(Q(9, 10) ** i for i in range(10)), 1)
    nums['ChainTen'] = dec(100 * (1 - Q(19, 20) ** 10), 1)

    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by grades.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
