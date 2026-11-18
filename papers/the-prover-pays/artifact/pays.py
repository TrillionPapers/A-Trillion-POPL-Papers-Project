#!/usr/bin/env python3
"""Tests the claims of "The Prover Pays" on an implementation of its checker.

The file has six parts.

1. Terms, definitions, and a second evaluator that the tests use as a reference.
2. The machine: weak head reduction by need, with a counter of steps and a limit.
3. The conversion test with advice, and policies that give advice.
4. The search for the cheapest advice, and the adversary of Theorem 5.1.
5. Types and the checker of proofs: a proof is a term, advice, and a price.
6. The tests.  `python3 pays.py out` writes out/check.txt, out/numbers.tex and the tables.

A test is not a proof.  The proofs are in the paper.
"""
import os
import random
import sys

sys.setrecursionlimit(400000)

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. Terms, with de Bruijn indices:
#      ('var', i) | ('lam', t) | ('app', t, u) | ('const', c) | ('zero',) | ('succ', t)
#      | ('rec', z, s, n) | ('refl',)
#    and types, which contain terms:  ('nat',) | ('pi', A, B) | ('eq', A, t, u).
#    rec z s 0 = z and rec z s (succ n) = s n (rec z s n).
# ---------------------------------------------------------------------------------------------

ZERO = ('zero',)


def var(i):
    return ('var', i)


def lam(t):
    return ('lam', t)


def app(f, *args):
    for a in args:
        f = ('app', f, a)
    return f


def const(c):
    return ('const', c)


def num(n):
    t = ZERO
    for _ in range(n):
        t = ('succ', t)
    return t


def rec(z, s, n):
    return ('rec', z, s, n)


# The library: every later definition may use the earlier ones.  The rank of a constant is its
# position in this list.
LIBRARY = [
    ('id', lam(var(0))),
    ('const0', lam(ZERO)),
    ('add', lam(lam(rec(var(0), lam(lam(('succ', var(0)))), var(1))))),            # add m n, by recursion on m
    ('double', lam(app(const('add'), var(0), var(0)))),
    ('mul', lam(lam(rec(ZERO, lam(lam(app(const('add'), var(2), var(0)))), var(1))))),   # mul m n
    ('pow2', lam(rec(num(1), lam(lam(app(const('double'), var(0)))), var(0)))),   # 2 to the n
    ('wrap', lam(var(0))),                                                          # an identity defined late
    ('pred', lam(rec(ZERO, lam(lam(var(1))), var(0)))),
    ('even', lam(rec(num(1), lam(lam(rec(num(1), lam(lam(ZERO)), var(0)))), var(0)))),   # 1 for an even number, 0 for an odd one
]
# A power of two that uses no other definition, and an identity: the adversary of Theorem 5.1
# gives these two bodies to an early and a late constant, in the order that hurts.
BIG = lam(rec(num(1), lam(lam(rec(var(0), lam(lam(('succ', var(0)))), var(0)))), var(0)))
SMALL = lam(var(0))
LIBRARY = [('early', SMALL)] + LIBRARY + [('late', SMALL)]
DEFS = dict(LIBRARY)
RANK = {name: i for i, (name, _) in enumerate(LIBRARY)}


def denote(t, env=()):
    """The reference: the value of a term as a Python number or function.  It shares nothing
    with the machine."""
    k = t[0]
    if k == 'var':
        return env[t[1]]
    if k == 'lam':
        return lambda x: denote(t[1], (x,) + env)
    if k == 'app':
        return denote(t[1], env)(denote(t[2], env))
    if k == 'const':
        return denote(DEFS[t[1]])
    if k == 'zero':
        return 0
    if k == 'succ':
        return denote(t[1], env) + 1
    if k == 'rec':
        z, s, n = denote(t[1], env), denote(t[2], env), denote(t[3], env)
        for i in range(n):
            z = s(i)(z)
        return z
    raise ValueError(t)


# ---------------------------------------------------------------------------------------------
# 2. The machine.  Values in weak head normal form:
#      ('vlam', env, body) | ('vne', head, spine) | ('vzero',) | ('vsucc', thunk) | ('vrefl',)
#      | ('vnat',) | ('vpi', thunk, env, body) | ('veq', thunk, thunk, thunk)
#    A head is ('lvl', k), a variable, or ('const', c), a constant that has not been unfolded.
#    A spine is a tuple of ('app', thunk) and ('rec', thunk, thunk).  An environment is a
#    linked list (thunk, rest).  Every step of the machine and of the test is counted, and the
#    machine stops when the count passes the limit.
# ---------------------------------------------------------------------------------------------

class Out(Exception):
    """The price is used up."""


class Thunk:
    """A term with its environment, evaluated when it is needed and at most once."""
    __slots__ = ('machine', 'term', 'env', 'value')

    def __init__(self, machine, term, env, value=None):
        self.machine, self.term, self.env, self.value = machine, term, env, value

    def force(self):
        if self.value is None:
            value = self.machine.eval(self.term, self.env)
            if MUTANT == 'by-name':
                return value
            self.value = value
        return self.value


class Later:
    """The value of rec z s m, computed when it is needed and at most once."""
    __slots__ = ('machine', 'z', 's', 'm', 'value')

    def __init__(self, machine, z, s, m):
        self.machine, self.z, self.s, self.m, self.value = machine, z, s, m, None

    def force(self):
        if self.value is None:
            value = self.machine.rec(self.z, self.s, self.m.force())
            if MUTANT == 'by-name':
                return value
            self.value = value
        return self.value


class Machine:
    def __init__(self, price, policy, defs=None):
        self.price, self.policy, self.steps, self.asked = price, policy, 0, 0
        self.defs = DEFS if defs is None else defs
        self.log = None                     # a list, to record what the test asks and unfolds

    def tick(self):
        self.steps += 1
        if self.steps > self.price:
            raise Out

    def eval(self, t, env):
        """Weak head reduction without unfolding constants."""
        self.tick()
        k = t[0]
        if k == 'var':
            for _ in range(t[1]):
                env = env[1]
            return env[0].force()
        if k == 'lam':
            return ('vlam', env, t[1])
        if k == 'app':
            return self.apply(self.eval(t[1], env), Thunk(self, t[2], env))
        if k == 'const':
            return ('vne', ('const', t[1]), ())
        if k == 'zero':
            return ('vzero',)
        if k == 'succ':
            return ('vsucc', Thunk(self, t[1], env))
        if k == 'rec':
            return self.rec(Thunk(self, t[1], env), Thunk(self, t[2], env), self.eval(t[3], env))
        if k == 'refl':
            return ('vrefl',)
        if k == 'nat':
            return ('vnat',)
        if k == 'pi':
            return ('vpi', Thunk(self, t[1], env), env, t[2])
        if k == 'eq':
            return ('veq', Thunk(self, t[1], env), Thunk(self, t[2], env), Thunk(self, t[3], env))
        raise ValueError(t)

    def apply(self, f, arg):
        self.tick()
        if f[0] == 'vlam':
            return self.eval(f[2], (arg, f[1]))
        if f[0] == 'vne':
            return ('vne', f[1], f[2] + (('app', arg),))
        raise ValueError('not a function')

    def rec(self, z, s, n):
        self.tick()
        if n[0] == 'vzero':
            return z.force()
        if n[0] == 'vsucc':
            return self.apply(self.apply(s.force(), n[1]), Later(self, z, s, n[1]))
        if n[0] == 'vne':
            return ('vne', n[1], n[2] + (('rec', z, s),))
        raise ValueError('not a number')

    def unfold(self, v):
        """Replaces the constant at the head by its definition and reduces to weak head form."""
        self.tick()
        if self.log is not None:
            self.log.append((self.steps, 'unfold', v[1][1]))
        r = self.eval(self.defs[v[1][1]], None)
        for e in v[2]:
            r = self.apply(r, e[1]) if e[0] == 'app' else self.rec(e[1], e[2], r)
        return r

    def fresh(self, lvl):
        return Thunk(self, None, None, ('vne', ('lvl', lvl), ()))

    # -----------------------------------------------------------------------------------------
    # 3. The test.  conv(a, b, lvl) decides whether two values are convertible.  Where both
    #    heads are constants, the policy is asked what to do: 'L' unfolds the left one, 'R' the
    #    right one, 'B' both, and 'S', for the same constant, compares the arguments first.
    # -----------------------------------------------------------------------------------------

    def conv(self, a, b, lvl=0):
        self.tick()
        if a is b:
            return True
        ka, kb = a[0], b[0]
        sa = ka == 'vne' and a[1][0] == 'const'
        sb = kb == 'vne' and b[1][0] == 'const'
        if sa or sb:
            return self.delta(a, b, lvl, sa, sb)
        if ka == 'vlam' or kb == 'vlam':
            if MUTANT == 'no-eta' and ka != kb:
                return False
            if not (ka in ('vlam', 'vne') and kb in ('vlam', 'vne')):
                return False
            x = self.fresh(lvl)
            return self.conv(self.apply(a, x), self.apply(b, x), lvl + 1)
        if ka != kb:
            return False
        if ka in ('vzero', 'vrefl', 'vnat'):
            return True
        if ka == 'vsucc':
            return self.conv(a[1].force(), b[1].force(), lvl)
        if ka == 'vne':
            return a[1] == b[1] and self.spines(a[2], b[2], lvl)
        if ka == 'vpi':
            if not self.conv(a[1].force(), b[1].force(), lvl):
                return False
            x = self.fresh(lvl)
            return self.conv(self.eval(a[3], (x, a[2])), self.eval(b[3], (x, b[2])), lvl + 1)
        if ka == 'veq':
            return all(self.conv(a[i].force(), b[i].force(), lvl) for i in (1, 2, 3))
        raise ValueError(ka)

    def spines(self, sa, sb, lvl):
        if len(sa) != len(sb):
            return False
        for x, y in zip(sa, sb):
            if x[0] != y[0]:
                return False
            for p, q in zip(x[1:], y[1:]):
                if p is not q and not self.conv(p.force(), q.force(), lvl):
                    return False
        return True

    def delta(self, a, b, lvl, sa, sb):
        if sa and sb:
            same = a[1] == b[1] and len(a[2]) == len(b[2])
            self.asked += 1
            choice = self.policy(a[1][1], b[1][1], same)
            if self.log is not None:
                self.log.append((self.steps, 'ask', a[1][1], b[1][1], choice if choice != 'S' or same else 'B'))
            if choice == 'S' and same:
                if self.spines(a[2], b[2], lvl):
                    return True
                if MUTANT == 'no-fallback':
                    return False
                choice = 'B'
            if choice == 'L':
                return self.conv(self.unfold(a), b, lvl)
            if choice == 'R':
                return self.conv(a, self.unfold(b), lvl)
            return self.conv(self.unfold(a), self.unfold(b), lvl)
        if MUTANT == 'one-sided' and sb and not sa:
            return False
        if sa:
            return self.conv(self.unfold(a), b, lvl)
        return self.conv(a, self.unfold(b), lvl)


# policies: functions of the two constants at the heads and of whether they are the same

def left(c, d, same):
    return 'L'


def right(c, d, same):
    return 'R'


def both(c, d, same):
    return 'B'


def args_first(c, d, same):
    return 'S' if same else 'B'


def later_first(c, d, same):
    """The constant that was defined later is unfolded first; arguments first for the same one."""
    return 'S' if same else 'L' if RANK[c] > RANK[d] else 'R'


def earlier_first(c, d, same):
    return 'S' if same else 'L' if RANK[c] < RANK[d] else 'R'


POLICIES = {'left': left, 'right': right, 'both': both, 'arguments first': args_first,
            'later first': later_first, 'earlier first': earlier_first}


class Need(Exception):
    def __init__(self, same):
        self.same = same


def oracle(advice, more=None):
    """The policy that reads its answers from a string.  When the string is used up it answers
    'B', or, for the search, reports what it was asked."""
    it = iter(advice)

    def policy(c, d, same):
        x = next(it, None)
        if x is None:
            if more is not None:
                raise Need(same)
            return 'B'
        return x if x != 'S' or same else 'B'

    return policy


YES, NO, OUT = 'yes', 'no', 'out'


def check(t, u, policy, price, defs=None):
    """The advised and metered test of Definition 4.1: the verdict and the steps taken."""
    m = Machine(price, policy, defs)
    try:
        verdict = YES if m.conv(m.eval(t, None), m.eval(u, None)) else NO
    except Out:
        if MUTANT == 'out-is-yes':
            return YES, m.steps
        return OUT, m.steps
    return verdict, m.steps


# ---------------------------------------------------------------------------------------------
# 4. The cheapest advice, by trying every string of answers, cheapest first; and the adversary.
# ---------------------------------------------------------------------------------------------

SEARCH = {'runs': 0, 'steps': 0}


def cheapest(t, u, limit, depth=8, defs=None):
    """The least number of steps over all advice of at most `depth` answers, with the advice
    and the verdict; None if no advice finishes within `limit` steps."""
    best = [None]

    def search(prefix):
        bound = limit if best[0] is None else best[0][0] - 1
        m = Machine(bound, oracle(prefix, more=len(prefix) < depth or None), defs)
        SEARCH['runs'] += 1
        try:
            try:
                verdict = YES if m.conv(m.eval(t, None), m.eval(u, None)) else NO
            finally:
                SEARCH['steps'] += min(m.steps, bound)
        except Out:
            return
        except Need as need:
            for x in (('S',) if need.same else ()) + ('L', 'R', 'B'):
                search(prefix + x)
            return
        best[0] = (m.steps, prefix, verdict)

    search('')
    return best[0]


def adversary(policy, n):
    """Theorem 5.1: a pair of terms, with definitions for the constants `early` and `late`, on
    which the policy is slow and some advice is fast.  The policy is asked what it would do,
    and the pair is built against its answers.  Returns the pair, the definitions, and the
    name of the case."""
    heavy = dict(DEFS, early=BIG, late=SMALL)
    big = app(const('early'), num(n))
    if policy('const0', 'const0', True) == 'S':
        # arguments first: the arguments are expensive and different, and the function ignores them
        return app(const('const0'), big), app(const('const0'), app(const('early'), num(n + 1))), heavy, 'ignored arguments'
    if policy('early', 'early', True) != 'S':
        # unfolding first: the arguments are cheap and equal
        return big, app(const('early'), num(n)), heavy, 'equal arguments'
    if policy('early', 'late', False) in ('L', 'B'):
        # the left constant is unfolded: let it be the expensive one, and the right one a wrapper of it
        defs = dict(DEFS, early=BIG, late=SMALL)
        return app(const('early'), num(n)), app(const('late'), app(const('early'), num(n))), defs, 'wrapper on the right'
    defs = dict(DEFS, early=SMALL, late=BIG)
    return app(const('early'), app(const('late'), num(n))), app(const('late'), num(n)), defs, 'wrapper on the left'


def table_policy(rng):
    """A random policy that decides by the ranks of the two constants and by whether they are
    the same."""
    table = {}

    def policy(c, d, same):
        key = (RANK[c], RANK[d], same)
        if key not in table:
            table[key] = ('SLRB' if same else 'LRB')[int(rng.random() * (4 if same else 3))]
        return table[key]

    return policy


# ---------------------------------------------------------------------------------------------
# 5. Proofs.  The only way to prove an equation here is by computation: `refl` proves
#    eq A t u when t and u are convertible.  A proof is a term, advice, and a price.
# ---------------------------------------------------------------------------------------------

class Refuse(Exception):
    pass


class Checker:
    """Checks a term against a type.  Every use of conversion takes its answers from one
    string of advice and its steps from one price."""

    def __init__(self, advice, price, defs, types):
        self.m = Machine(price, oracle(advice), defs)
        self.types = types                  # constant -> type, a closed term

    def is_type(self, ctx, env, a):
        k = a[0]
        if k == 'nat':
            return
        if k == 'pi':
            self.is_type(ctx, env, a[1])
            dom = self.m.eval(a[1], env)
            x = self.m.fresh(len(ctx))
            self.is_type(ctx + [dom], (x, env), a[2])
        elif k == 'eq':
            self.is_type(ctx, env, a[1])
            ty = self.m.eval(a[1], env)
            self.check(ctx, env, a[2], ty)
            self.check(ctx, env, a[3], ty)
        else:
            raise Refuse('not a type')

    def check(self, ctx, env, t, ty):
        k = t[0]
        if k == 'lam':
            if ty[0] != 'vpi':
                raise Refuse('a function needs a function type')
            x = self.m.fresh(len(ctx))
            self.check(ctx + [ty[1].force()], (x, env), t[1], self.m.eval(ty[3], (x, ty[2])))
        elif k == 'refl':
            if ty[0] != 'veq':
                raise Refuse('refl needs an equation')
            if not self.m.conv(ty[2].force(), ty[3].force(), len(ctx)):
                raise Refuse('the two sides are not convertible')
        else:
            got = self.infer(ctx, env, t)
            if not self.m.conv(got, ty, len(ctx)):
                raise Refuse('wrong type')

    def infer(self, ctx, env, t):
        k = t[0]
        if k == 'var':
            return ctx[len(ctx) - 1 - t[1]]
        if k == 'const':
            return self.m.eval(self.types[t[1]], None)
        if k == 'zero':
            return ('vnat',)
        if k == 'succ':
            self.check(ctx, env, t[1], ('vnat',))
            return ('vnat',)
        if k == 'app':
            f = self.infer(ctx, env, t[1])
            if f[0] != 'vpi':
                raise Refuse('not a function')
            self.check(ctx, env, t[2], f[1].force())
            return self.m.eval(f[3], (Thunk(self.m, t[2], env), f[2]))
        if k == 'rec':                      # at the type of numbers only
            self.check(ctx, env, t[1], ('vnat',))
            nat_nat_nat = self.m.eval(('pi', ('nat',), ('pi', ('nat',), ('nat',))), None)
            self.check(ctx, env, t[2], nat_nat_nat)
            self.check(ctx, env, t[3], ('vnat',))
            return ('vnat',)
        raise Refuse('cannot infer')


def check_proof(ty, term, advice, price, defs, types):
    """Whether the proof is accepted, and the steps that the check took."""
    c = Checker(advice, price, defs, types)
    try:
        c.is_type([], None, ty)
        c.check([], None, term, c.m.eval(ty, None))
        return YES, c.m.steps
    except Refuse:
        return NO, c.m.steps
    except Out:
        return OUT, c.m.steps


NAT = ('nat',)
TYPES = {'early': ('pi', NAT, NAT), 'late': ('pi', NAT, NAT), 'id': ('pi', NAT, NAT), 'const0': ('pi', NAT, NAT), 'add': ('pi', NAT, ('pi', NAT, NAT)),
         'double': ('pi', NAT, NAT), 'mul': ('pi', NAT, ('pi', NAT, NAT)), 'pow2': ('pi', NAT, NAT),
         'wrap': ('pi', NAT, NAT), 'pred': ('pi', NAT, NAT), 'even': ('pi', NAT, NAT)}


def equation(t, u):
    return ('eq', NAT, t, u)


# ---------------------------------------------------------------------------------------------
# 6. The tests.
# ---------------------------------------------------------------------------------------------

def random_nat(rng, depth):
    """A closed term for a number, small enough to evaluate."""
    x = rng.random()
    if depth == 0 or x < 0.2:
        return num(int(rng.random() * 4))
    sub = lambda: random_nat(rng, depth - 1)
    if x < 0.32:
        return ('succ', sub())
    if x < 0.46:
        return app(const('add'), sub(), sub())
    if x < 0.54:
        return app(const('double'), sub())
    if x < 0.60:
        return app(const('mul'), num(int(rng.random() * 3)), sub())
    if x < 0.66:
        return app(const('pow2'), num(int(rng.random() * 4)))
    if x < 0.74:
        return app(const(('id', 'wrap')[int(rng.random() * 2)]), sub())
    if x < 0.80:
        return app(const('const0'), sub())
    if x < 0.86:
        return app(const('pred'), sub())
    if x < 0.93:
        return app(lam(app(const('add'), var(0), var(0))), sub())
    return rec(sub(), lam(lam(('succ', var(0)))), num(int(rng.random() * 3)))


def random_advice(rng):
    return ''.join('SLRB'[int(rng.random() * 4)] for _ in range(int(rng.random() * 10)))


def trial(rng, counts):
    """Theorems 4.2 to 4.4 on one random pair of numbers: the verdict is that of the reference
    under every policy and every advice, it does not depend on the advice, the steps never
    pass the price, and a price that is too small gives `out` and never a wrong answer."""
    t = random_nat(rng, 4)
    u = t if rng.random() < 0.15 else random_nat(rng, 4)
    if rng.random() < 0.3:                  # a pair that is equal for a reason
        u = app(const('add'), num(0), t) if rng.random() < 0.5 else app(const('id'), t)
    want = YES if denote(t) == denote(u) else NO
    costs = {}
    for name, policy in POLICIES.items():
        verdict, steps = check(t, u, policy, 10 ** 7)
        assert verdict == want, (name, verdict, want)
        costs[name] = steps
    for _ in range(3):
        advice = random_advice(rng)
        verdict, steps = check(t, u, oracle(advice), 10 ** 7)
        assert verdict == want, (advice, verdict, want)
        small = int(rng.random() * steps)
        v2, s2 = check(t, u, oracle(advice), small)
        assert v2 == OUT and s2 == small + 1, 'a price that is too small must give out'
        v3, s3 = check(t, u, oracle(advice), steps)
        assert (v3, s3) == (verdict, steps), 'the exact price must do'
    counts['pairs'] += 1
    counts[want] += 1
    return t, u, want, costs


def user_equation(rng):
    """An equation of the kinds that users write: a term against itself under identities, a
    unit law, a doubling, a function that ignores its argument.  Both sides are convertible."""
    n = 5 + int(rng.random() * 4)
    x = app(const('pow2'), num(n))
    wrapper = lambda t: app(const(('id', 'wrap')[int(rng.random() * 2)]), t)
    k = int(rng.random() * 7)
    if k == 0:
        t, u = x, wrapper(x)
    elif k == 1:
        t, u = wrapper(wrapper(x)), x
    elif k == 2:
        t, u = app(const('add'), num(0), x), x
    elif k == 3:
        t, u = app(const('double'), x), app(const('add'), x, x)
    elif k == 4:
        t, u = app(const('pow2'), num(n + 1)), app(const('double'), x)
    elif k == 5:
        t, u = app(const('const0'), x), app(const('const0'), app(const('pow2'), num(n + 1)))
    else:
        t, u = app(const('double'), wrapper(x)), app(const('double'), x)
    return (u, t) if rng.random() < 0.5 else (t, u)


MUTANTS = ('out-is-yes', 'no-fallback', 'one-sided', 'no-eta', 'by-name')


def catches(name):
    """Whether the tests notice the mistake: the random pairs, or the pairs under binders, or
    the cost of the family that needs sharing."""
    global MUTANT
    MUTANT = name
    try:
        rng, counts = random.Random(2026), {'pairs': 0, YES: 0, NO: 0}
        for _ in range(400):
            trial(rng, counts)
        binders()
        sharing()
        return False
    except AssertionError:
        return True
    finally:
        MUTANT = None


def binders():
    """Conversion under binders: eta, and variables with spines."""
    ident = lam(var(0))
    pairs = [(const('id'), ident, YES), (lam(app(const('id'), var(0))), const('id'), YES),
             (lam(app(const('add'), num(0), var(0))), ident, YES),
             (lam(app(const('add'), var(0), num(0))), ident, NO),          # needs induction
             (lam(lam(app(var(1), var(0)))), ident, YES),                   # eta
             (lam(app(const('const0'), var(0))), const('const0'), YES),
             (lam(('succ', var(0))), lam(app(const('add'), num(1), var(0))), YES),
             (lam(('succ', var(0))), ident, NO)]
    for t, u, want in pairs:
        for policy in POLICIES.values():
            assert check(t, u, policy, 10 ** 6)[0] == want, (t, u)
            assert check(u, t, policy, 10 ** 6)[0] == want, (u, t)
    return len(pairs)


def sharing():
    """A value that is needed twice is computed once: the second use takes no step."""
    m = Machine(10 ** 7, both)
    thunk = Thunk(m, app(const('add'), num(20), num(20)), None)
    m.conv(thunk.force(), m.eval(num(40), None))
    first = m.steps
    m.conv(thunk.force(), thunk.force())
    assert m.steps == first + 1, (first, m.steps)
    return first


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten']

    # the library is what it claims to be
    assert denote(app(const('add'), num(2), num(3))) == 5 and denote(app(const('mul'), num(3), num(4))) == 12
    assert denote(app(const('pow2'), num(6))) == 64 and denote(app(const('pred'), num(3))) == 2

    # Theorems 4.2 to 4.4
    counts, worse, total = {'pairs': 0, YES: 0, NO: 0}, {name: 0 for name in POLICIES}, {name: 0 for name in POLICIES}
    searched = found_better = 0
    ratios = []
    for i in range(3000):
        t, u, want, costs = trial(rng, counts)
        for name in POLICIES:
            total[name] += costs[name]
        if i % 5 == 0:
            best = cheapest(t, u, min(costs.values()), depth=6)
            assert best is None or best[2] == want
            least = min(costs.values()) if best is None else min(best[0], min(costs.values()))
            searched += 1
            found_better += least < min(costs.values())
            for name in POLICIES:
                worse[name] += costs[name] > least
            ratios.append(max(costs.values()) / least)
    claim('verdicts', counts['pairs'] == 3000)
    lines.append(f"{counts['pairs']} random pairs of numbers, {counts[YES]} convertible: the verdict is that of the "
                 f"reference under {len(POLICIES)} policies and three random advices each; a smaller price gives out")
    lines.append(f'{searched} of the pairs searched for the cheapest advice: it is cheaper than every policy for '
                 f'{found_better}; the largest ratio between a policy and the cheapest advice is {max(ratios):.1f}')
    lines.append('policies beaten by the cheapest advice on the searched pairs: ' +
                 ', '.join(f'{name} {n}' for name, n in worse.items()))
    nums.update(Pairs=f"{counts['pairs']:,}", Convertible=f"{counts[YES]:,}", Searched=str(searched),
                Better=str(found_better), Ratio=f'{max(ratios):.1f}', Policies=spelled[len(POLICIES)])
    n_binders = binders()
    claim('binders', True)
    lines.append(f'{n_binders} pairs under binders, in both directions and under every policy: as expected')
    nums['Binders'] = spelled[n_binders]
    first = sharing()
    claim('sharing', True)
    lines.append(f'a value that is needed again is not computed again: {first} steps the first time, one step the second')

    # Theorem 5.1: every policy by ranks has a family on which it is slow
    rows, sizes = [], (4, 6, 8, 10)
    for name, policy in POLICIES.items():
        steps, quick, case = [], [], None
        for n in sizes:
            t, u, defs, case = adversary(policy, n)
            verdict, k = check(t, u, policy, 10 ** 8, defs)
            best = cheapest(t, u, k, depth=3, defs=defs)
            assert best[2] == verdict
            steps.append(k)
            quick.append(best[0])
        assert all(b >= 3 * a for a, b in zip(steps, steps[1:])), (name, steps)
        assert all(b - a <= 40 for a, b in zip(quick, quick[1:])), (name, quick)
        lines.append(f'{name}, {case}: ' + ', '.join(f'n={n}: {a} against {b}' for n, a, b in zip(sizes, steps, quick)))
        rows.append(f"{name} & {case} & " + ' & '.join(f'{a:,}' for a in steps) + f' & {quick[-1]} \\\\')
    tables['adversary'] = rows
    fooled, late_cases = 0, 0
    for _ in range(300):
        policy = table_policy(rng)
        slow, fast = [], []
        for n in (5, 9):
            t, u, defs, case = adversary(policy, n)
            _, k = check(t, u, policy, 10 ** 8, defs)
            slow.append(k)
            fast.append(cheapest(t, u, k, depth=3, defs=defs)[0])
        fooled += slow[1] >= 8 * slow[0] and fast[1] - fast[0] <= 60
        late_cases += case.startswith('wrapper')
    claim('adversary', fooled == 300 and late_cases > 0)
    lines.append(f'{fooled} of 300 random policies by ranks: from n=5 to n=9 the steps of the policy grow at least '
                 'eightfold and those of the cheapest advice by at most 60')
    nums.update(RandomPolicies='300', AdversaryLargest=str(sizes[-1]), CaseThree=str(late_cases))

    # Table 3: eight equations under the six policies
    power = lambda k: app(const('pow2'), num(k))
    equations = [
        ('\\nm{pow2}\\ 10 = \\nm{id}\\ (\\nm{pow2}\\ 10)', power(10), app(const('id'), power(10))),
        ('\\nm{wrap}\\ (\\nm{pow2}\\ 10) = \\nm{pow2}\\ 10', app(const('wrap'), power(10)), power(10)),
        ('\\nm{const0}\\ (\\nm{pow2}\\ 10) = \\nm{const0}\\ (\\nm{pow2}\\ 11)', app(const('const0'), power(10)),
         app(const('const0'), power(11))),
        ('\\nm{add}\\ 0\\ (\\nm{pow2}\\ 10) = \\nm{pow2}\\ 10', app(const('add'), num(0), power(10)), power(10)),
        ('\\nm{double}\\ (\\nm{pow2}\\ 9) = \\nm{pow2}\\ 10', app(const('double'), power(9)), power(10)),
        ('\\nm{pow2}\\ 10 = \\nm{pow2}\\ 10', power(10), app(const('pow2'), num(10))),
        ('\\nm{mul}\\ 2\\ (\\nm{pow2}\\ 9) = \\nm{pow2}\\ 10', app(const('mul'), num(2), power(9)), power(10)),
        ('\\nm{pred}\\ (\\nm{pow2}\\ 5) = 31', app(const('pred'), power(5)), num(31)),
    ]
    rows, winners, spread = [], set(), []
    for label, t, u in equations:
        costs = {name: check(t, u, policy, 10 ** 8)[1] for name, policy in POLICIES.items()}
        assert all(check(t, u, policy, 10 ** 8)[0] == YES for policy in POLICIES.values())
        best = cheapest(t, u, min(costs.values()), depth=5)
        least = min(min(costs.values()), best[0] if best else 10 ** 9)
        winners.add(tuple(sorted(name for name, k in costs.items() if k == min(costs.values()))))
        spread.append(max(costs.values()) / least)
        lines.append('equation ' + label.replace('\\nm', '').replace('\\', '') + ': ' +
                     ', '.join(f'{name} {k}' for name, k in costs.items()) + f', least found {least}')
        rows.append(f'${label}$ & ' + ' & '.join(f'{k:,}' for k in costs.values()) + f' & {least:,} \\\\')
    tables['equations'] = rows
    claim('equations', len(winners) >= 3 and sum(x > 100 for x in spread) >= 5 and min(spread) == 1)
    nums['Equations'] = spelled[len(equations)]

    # Table 4: random equations of the kinds that users write
    stats = {name: [0, 0, 0.0] for name in POLICIES}        # within twice the least, over a hundred times, largest ratio
    n_user = 200
    for _ in range(n_user):
        t, u = user_equation(rng)
        costs = {name: check(t, u, policy, 10 ** 9)[1] for name, policy in POLICIES.items()}
        best = cheapest(t, u, min(costs.values()), depth=4)
        least = min(min(costs.values()), best[0] if best else 10 ** 12)
        for name, k in costs.items():
            stats[name][0] += k <= 2 * least
            stats[name][1] += k > 100 * least
            stats[name][2] = max(stats[name][2], k / least)
    rows = []
    for name, (near, far, worst) in stats.items():
        lines.append(f'{n_user} user equations, {name}: within twice the least for {near}, over a hundred times for {far}, '
                     f'largest ratio {worst:.0f}')
        rows.append(f'{name} & {near} & {far} & {worst:,.0f} \\\\')
    tables['users'] = rows
    claim('users', all(far > 0 for _, far, _ in stats.values()) and max(near for near, _, _ in stats.values()) < n_user)
    nums['UserEquations'] = str(n_user)

    # the search of the prover, for the equation of Section 2
    SEARCH.update(runs=0, steps=0)
    found = cheapest(power(10), app(const('id'), power(10)), 10 ** 8, depth=3)
    claim('search', found[1] == 'RS' and SEARCH['steps'] < 10 ** 8)
    lines.append(f"searching the advice of the first equation: {SEARCH['runs']} runs of the test, {SEARCH['steps']} "
                 f'steps in all, for an advice that checks in {found[0]}')
    nums.update(SearchRuns=str(SEARCH['runs']), SearchSteps=f"{SEARCH['steps']:,}")

    # Proposition 6.4: the order of two definitions
    wrapper_late = (dict(DEFS, early=BIG, late=SMALL), app(const('early'), num(10)),
                    app(const('late'), app(const('early'), num(10))))
    wrapper_early = (dict(DEFS, early=SMALL, late=BIG), app(const('late'), num(10)),
                     app(const('early'), app(const('late'), num(10))))
    order = {}
    for key, (defs_, t, u) in (('late', wrapper_late), ('early', wrapper_early)):
        order[key] = (check(t, u, later_first, 10 ** 8, defs_)[1], check(t, u, earlier_first, 10 ** 8, defs_)[1],
                      check(t, u, oracle('RS'), 10 ** 8, defs_)[1])
    claim('order', order['late'][2] == order['early'][2] and order['early'][0] > 100 * order['late'][0]
          and order['late'][1] > 100 * order['early'][1])
    lines.append(f"a wrapper defined after or before the function that it wraps: later first {order['late'][0]} and "
                 f"{order['early'][0]} steps, earlier first {order['late'][1]} and {order['early'][1]}, advice RS "
                 f"{order['late'][2]} and {order['early'][2]}")
    nums.update(OrderGood=str(order['late'][0]), OrderBad=f"{order['early'][0]:,}", OrderAdvice=str(order['late'][2]))

    # Section 6: proofs with prices
    n10 = num(10)
    theorems = [
        ('four', equation(app(const('add'), num(2), num(2)), num(4)), ('refl',), ''),
        ('sixteen', equation(app(const('pow2'), num(4)), app(const('mul'), num(4), num(4))), ('refl',), ''),
        ('wrapped', equation(app(const('pow2'), n10), app(const('id'), app(const('pow2'), n10))), ('refl',), 'RS'),
        ('ignored', equation(app(const('const0'), app(const('pow2'), n10)), app(const('const0'), app(const('pow2'), num(11)))),
         ('refl',), 'B'),
        ('parity', equation(app(const('even'), app(const('pow2'), num(6))), num(1)), ('refl',), ''),
        ('unit', ('pi', NAT, equation(app(const('add'), num(0), var(0)), var(0))), lam(('refl',)), ''),
        ('use', equation(app(const('add'), num(0), app(const('pow2'), n10)), app(const('pow2'), n10)),
         app(const('unit'), app(const('pow2'), n10)), 'SSS'),
    ]
    wrapped = (app(const('pow2'), n10), app(const('id'), app(const('pow2'), n10)))
    blind, advised, slow = (check(*wrapped, oracle(a), 10 ** 8) for a in ('', 'RS', 'L'))
    claim('overview', blind[0] == YES and slow == blind[:1] + (slow[1],) and slow[1] > 1000 * advised[1])
    claim('advice-rs', advised[0] == YES and cheapest(*wrapped, 10 ** 4, depth=3)[0] == advised[1])
    lines.append(f"pow2 10 against id (pow2 10): {blind[1]} steps without advice, {advised[1]} with RS, {slow[1]} with L")
    nums.update(OverviewBlind=f'{blind[1]:,}', OverviewAdvised=str(advised[1]))
    rows, logs = [], {}
    for advice in ('RS', 'L'):
        m = Machine(10 ** 8, oracle(advice))
        m.log = []
        assert m.conv(m.eval(wrapped[0], None), m.eval(wrapped[1], None))
        logs[advice] = len(m.log)
        for event in m.log[:5]:
            if event[1] == 'ask':
                what = f"$\\nm{{{event[2]}}}$ against $\\nm{{{event[3]}}}$: the advice says \\adv{{{event[4]}}}"
            else:
                what = f"unfold $\\nm{{{event[2]}}}$"
            rows.append(f'\\adv{{{advice}}} & {event[0]} & {what} \\\\')
            lines.append(f'walk with {advice}: step {event[0]}: ' + ' '.join(event[1:]))
        if len(m.log) > 5:
            rows.append(f'\\adv{{{advice}}} & & {len(m.log) - 5:,} more questions and unfoldings \\\\')
        rows.append(f'\\adv{{{advice}}} & {m.steps:,} & the two sides are convertible \\\\')
        if advice == 'RS':
            rows.append('\\midrule')
        lines.append(f'walk with {advice}: {len(m.log)} questions and unfoldings, yes after {m.steps} steps')
    tables['walk'] = rows
    claim('walk', logs['RS'] == 3 and logs['L'] > 1000)

    # Proposition 4.5: against a numeral that is written out, the test takes at least as many steps as the numeral is long
    for _ in range(300):
        t = random_nat(rng, 4)
        value = denote(t)
        for policy in POLICIES.values():
            assert check(t, num(value), policy, 10 ** 8)[1] >= value
        assert cheapest(t, num(value), 10 ** 8, depth=3)[0] >= value
    claim('literal', True)
    nums['LiteralPairs'] = '300'

    defs, types, rows, total, blind_total = dict(DEFS), dict(TYPES), [], 0, 0
    for name, ty, term, advice in theorems:
        verdict, price = check_proof(ty, term, advice, 10 ** 8, defs, types)
        assert verdict == YES, name
        assert check_proof(ty, term, advice, price, defs, types) == (YES, price)
        assert check_proof(ty, term, advice, price - 1, defs, types)[0] == OUT
        blind = check_proof(ty, term, '', 10 ** 8, defs, types)
        assert blind[0] == YES
        total += price
        blind_total += blind[1]
        lines.append(f"theorem {name}: advice '{advice}', price {price}; without advice {blind[1]} steps")
        rows.append(f"$\\nm{{{name}}}$ & {advice or '--'} & {price:,} & {blind[1]:,} \\\\")
        defs[name], types[name] = term, ty
    tables['theorems'] = rows
    wrong = check_proof(equation(num(2), num(3)), ('refl',), 'SLRB', 10 ** 6, defs, types)
    claim('theorems', wrong[0] == NO and blind_total > 20 * total and all(
        check_proof(equation(num(2), num(3)), ('refl',), a, 10 ** 6, defs, types)[0] == NO for a in ('', 'L', 'R', 'S', 'B')))
    lines.append(f'the library costs {total} steps with advice and {blind_total} without; a false equation is refused')
    nums.update(LibraryPrice=f'{total:,}', LibraryBlind=f'{blind_total:,}', LibraryRatio=f'{blind_total // total:,}',
                Theorems=spelled[len(theorems)])

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed: ' + ', '.join(MUTANTS))
    nums.update(Mutants=spelled[len(MUTANTS)], Seed='2026',
                Lines=f"{round(len(open(os.path.join(here, 'pays.py')).readlines()), -2):,}")

    paper = os.path.join(here, '..', 'paper.tex')
    if os.path.exists(paper):
        import re
        marked = set(re.findall(r'\\claim\{([a-z-]+)\}', open(paper).read()))
        assert marked == CLAIMS, (sorted(marked - CLAIMS), sorted(CLAIMS - marked))
    lines.append(f'{len(CLAIMS)} sentences of the paper checked: ' + ', '.join(sorted(CLAIMS)))

    os.makedirs(outdir, exist_ok=True)
    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by pays.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by pays.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
