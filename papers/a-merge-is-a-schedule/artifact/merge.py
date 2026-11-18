#!/usr/bin/env python3
"""Tests the claims of "A Merge Is a Schedule" on an implementation of its calculus.

The file has six parts.

1. Tasks and checks: programs that read and write the keys of a repository, ask a model, and
   run checks.
2. Runs.  A task runs on a base state with its own writes on top, and leaves a journal in
   which every request has its answer and its footprint.  The same code replays a journal on
   another state: it compares what has changed and asks the model nothing, until an answer
   differs.
3. The merge queue, and the reference: the tasks one after the other.
4. Random tasks and repositories.
5. Fleets: random footprints, the graph of stale reads, and the orders of a queue.
6. The import graph of a library, and the tests.  `python3 merge.py out` writes
   out/check.txt and out/numbers.tex.

A test is not a proof.  The proofs are in the paper.
"""
import os
import random
import sys
from fractions import Fraction
from itertools import count, permutations
from math import comb

KEYS, VALUES = 6, 4


# ---------------------------------------------------------------------------------------------
# 1. Terms ('c', n) | ('v', x) | ('add', s, t); tests ('eq', s, t) | ('le', s, t).  Expressions:
#    ('tm', t) | ('let', x, e, e) | ('if', test, e, e) | ('iter', n, t, x, e)
#    | ('read', t) | ('write', t, t) | ('model', t) | ('check', c) | ('scan',)
#    A check is an expression without write, model and check.
# ---------------------------------------------------------------------------------------------

def c(n):
    return ('c', n)


def v(x):
    return ('v', x)


def tval(t, env):
    if t[0] == 'c':
        return t[1]
    if t[0] == 'v':
        return env[t[1]]
    return tval(t[1], env) + tval(t[2], env)


def holds(test, env):
    a, b = tval(test[1], env) % VALUES, tval(test[2], env) % VALUES
    return a == b if test[0] == 'eq' else a <= b


# ---------------------------------------------------------------------------------------------
# 2. Runs.  Journal entries: ('read', k, v, F) | ('write', k, v) | ('model', c, r)
#    | ('check', c, v, F) | ('scan', v, F), where F is the footprint: the keys of the base
#    state on which the answer depends.
# ---------------------------------------------------------------------------------------------

BROKEN = None       # the name of a step of the replay that is deliberately broken

STEPS = ('skip-read', 'skip-check', 'scan-local', 'stale-delta', 'last-delta')


class Stream:
    """A model that answers from a random stream."""

    def __init__(self, seed):
        self.rng = random.Random(seed)

    def __call__(self):
        return int(self.rng.random() * VALUES)


class Script:
    """A model that gives the answers of a list, in order."""

    def __init__(self, answers):
        self.answers = list(answers)

    def __call__(self):
        return self.answers.pop(0)


class Run:
    """A run of a task on a base state.  Without a journal the run is live.  With a journal,
    and the set `delta` of keys on which the base differs from the base of the journal, it
    replays: a request whose footprint misses `delta` keeps its answer, another is made again
    and compared, the model is not asked, and at the first answer that differs the run goes
    live."""

    def __init__(self, base, checks, model, journal=None, delta=frozenset()):
        self.base, self.checks, self.model = base, checks, model
        self.old, self.delta, self.live = journal, delta, journal is None
        self.over, self.J, self.resumed = {}, [], None
        self.again = self.calls = 0     # requests made again in replay; model calls made

    def view(self, k):
        return self.over[k] if k in self.over else self.base[k]

    def query(self, q, env, F):
        """The value of a check on the view; the base keys that it reads are added to F."""
        k = q[0]
        if k == 'tm':
            return tval(q[1], env) % VALUES
        if k == 'let':
            return self.query(q[3], {**env, q[1]: self.query(q[2], env, F)}, F)
        if k == 'if':
            return self.query(q[2] if holds(q[1], env) else q[3], env, F)
        if k == 'iter':
            x = tval(q[2], env) % VALUES
            for _ in range(q[1]):
                x = self.query(q[4], {**env, q[3]: x}, F)
            return x
        if k == 'read':
            key = tval(q[1], env) % KEYS
            if key not in self.over:
                F.add(key)
            return self.view(key)
        F.update(key for key in range(KEYS) if key not in self.over)
        return sum(self.view(key) for key in range(KEYS)) % VALUES

    def perform(self, kind, what):
        """A read, a check or a scan on the view: its value and its footprint."""
        F = set()
        if kind == 'read':
            value = self.query(('read', c(what)), {}, F)
        elif kind == 'check':
            value = self.query(self.checks[what], {}, F)
        else:
            value = self.query(('scan',), {}, F)
            if BROKEN == 'scan-local':
                F = set()
        return value, frozenset(F)

    def answer(self, kind, what=None):
        """The answer to a read, a check or a scan."""
        if self.live:
            value, F = self.perform(kind, what)
        else:
            old = self.old[len(self.J)]
            assert old[:-2] == ((kind,) if what is None else (kind, what))
            value, F = old[-2], old[-1]
            skip = BROKEN == 'skip-' + kind
            if F & self.delta and not skip:             # something that the answer read has changed
                self.again += 1
                value, F = self.perform(kind, what)
                if value != old[-2]:
                    self.live, self.resumed = True, len(self.J)
        self.J.append(((kind,) if what is None else (kind, what)) + (value, F))
        return value

    def ev(self, e, env):
        k = e[0]
        if k == 'tm':
            return tval(e[1], env) % VALUES
        if k == 'let':
            return self.ev(e[3], {**env, e[1]: self.ev(e[2], env)})
        if k == 'if':
            return self.ev(e[2] if holds(e[1], env) else e[3], env)
        if k == 'iter':
            x = tval(e[2], env) % VALUES
            for _ in range(e[1]):
                x = self.ev(e[4], {**env, e[3]: x})
            return x
        if k == 'read':
            return self.answer('read', tval(e[1], env) % KEYS)
        if k == 'check':
            return self.answer('check', e[1])
        if k == 'scan':
            return self.answer('scan')
        if k == 'write':
            key, value = tval(e[1], env) % KEYS, tval(e[2], env) % VALUES
            assert self.live or self.old[len(self.J)] == ('write', key, value)
            self.over[key] = value
            self.J.append(('write', key, value))
            return value
        arg = tval(e[1], env) % VALUES
        if self.live:
            self.calls += 1
            r = self.model()
        else:
            old = self.old[len(self.J)]
            assert old[:2] == ('model', arg)            # the same question as before
            r = old[2]
        self.J.append(('model', arg, r))
        return r

    def run(self, task):
        self.value = self.ev(task, {})
        assert self.live or len(self.J) == len(self.old)
        return self


def footprint(J):
    return frozenset().union(*[entry[-1] for entry in J if entry[0] in ('read', 'check', 'scan')])


def plain(J):
    """A journal without its footprints: the requests and their answers."""
    return [entry[:-1] if entry[0] in ('read', 'check', 'scan') else entry for entry in J]


def answers(J):
    return [entry[2] for entry in J if entry[0] == 'model']


def changed(base, state):
    return frozenset(k for k in base if base[k] != state[k])


# ---------------------------------------------------------------------------------------------
# 3. The merge queue and the reference
# ---------------------------------------------------------------------------------------------

def merge(base, checks, tasks, runs, order, seed):
    """Replays the journals of tasks that ran on `base`, one after the other in `order`, each on
    the state that the earlier ones leave.  Returns the final state and the new runs."""
    state, new, stale, last = dict(base), {}, set(), frozenset()
    for i in order:
        delta = changed(base, state)
        if BROKEN == 'stale-delta':         # the writes that the earlier tasks made at first
            delta = frozenset(stale)
        if BROKEN == 'last-delta':          # the writes of the task just before
            delta = last
        new[i] = Run(state, checks, Stream(seed + i), runs[i].J, delta).run(tasks[i])
        last = changed(state, {**state, **new[i].over})
        state = {**state, **new[i].over}
        stale |= {k for k, value in runs[i].over.items() if value != base[k]}
    return state, new


def serial(base, checks, tasks, order, new):
    """The tasks one after the other, live, with the model answers of the given runs.  Checks
    that each run is the given one, entry by entry with its footprints, and returns the final
    state; None if a run differs."""
    state = dict(base)
    for i in order:
        model = Script(answers(new[i].J))
        try:
            live = Run(state, checks, model).run(tasks[i])
        except IndexError:                  # the live run asks the model more often
            return None
        if (live.J, live.over, live.value) != (new[i].J, new[i].over, new[i].value) or model.answers:
            return None
        state = {**state, **live.over}
    return state


def graph(base, runs):
    """An edge from i to j: i has read a key that j has changed."""
    return {i: {j for j in runs if j != i and footprint(runs[i].J) & changed(base, {**base, **runs[j].over})}
            for i in runs}


def topological(edges):
    """An order in which every edge goes forward, or None if there is a cycle."""
    order, left = [], {i: set(js) for i, js in edges.items()}
    while left:
        free = sorted(i for i in left if not any(i in js for js in left.values()))
        if not free:
            return None
        order.append(free[0])
        del left[free[0]]
    return order


def feedback(edges):
    """A smallest set of vertices whose removal leaves no cycle; exact, for small graphs."""
    nodes = sorted(edges)
    for size in range(len(nodes) + 1):
        for drop in map(set, combinations(nodes, size)):
            rest = {i: edges[i] - drop for i in nodes if i not in drop}
            if topological(rest) is not None:
                return drop


def combinations(xs, n):
    if n == 0:
        yield ()
    else:
        for i, x in enumerate(xs):
            for rest in combinations(xs[i + 1:], n - 1):
                yield (x,) + rest


# ---------------------------------------------------------------------------------------------
# 4. Random tasks and repositories
# ---------------------------------------------------------------------------------------------

class Gen:
    def __init__(self, rng):
        self.rng, self.names = rng, count()

    def below(self, n):
        return int(self.rng.random() * n)

    def one(self, xs):
        return xs[self.below(len(xs))]

    def term(self, env):
        r = self.rng.random()
        if env and r < 0.55:
            return v(self.one(env))
        if env and r < 0.7:
            return ('add', v(self.one(env)), c(1 + self.below(3)))
        return c(self.below(KEYS))

    def test(self, env):
        return (self.one(['eq', 'le']), self.term(env), self.term(env))

    def step(self, env, task):
        r = self.rng.random()
        if r < 0.4:
            return ('read', self.term(env))
        if r < 0.47:
            return ('scan',)
        if not task or r < 0.55:
            return ('tm', self.term(env))
        if r < 0.72:
            return ('write', self.term(env), self.term(env))
        if r < 0.86:
            return ('model', self.term(env))
        return ('check', self.below(3))

    def expr(self, depth, env, task):
        """A task, or with task = False a check."""
        if depth == 0:
            return self.step(env, task)
        k = self.one(['let'] * 7 + ['if', 'if', 'iter'])
        if k == 'let':
            x = 'x%d' % next(self.names)
            return ('let', x, self.step(env, task), self.expr(depth - 1, env + [x], task))
        if k == 'if':
            return ('if', self.test(env), self.expr(depth - 1, env, task), self.expr(depth - 1, env, task))
        x = 'x%d' % next(self.names)
        return ('iter', 1 + self.below(2), self.term(env), x, self.expr(depth - 1, env + [x], task))

    def repository(self):
        """A base state and three checks."""
        return ({k: self.below(VALUES) for k in range(KEYS)}, [self.expr(3, [], False) for _ in range(3)])

    def task(self):
        return self.expr(6, [], True)


def with_suite(task):
    """A task that ends with the three checks of its repository."""
    total = ('add', v('a'), ('add', v('b'), v('d')))
    tail = ('let', 'a', ('check', 0), ('let', 'b', ('check', 1), ('let', 'd', ('check', 2), ('tm', total))))
    return ('let', 'w', task, tail)


def skew(n):
    """n tasks on keys 0..n-1, all 1 at first.  Task i sets its key to 0 if the next key is 1.
    Each alone keeps the check `some key is 1`; all together break it."""
    tasks = [('let', 'x', ('read', c((i + 1) % n)),
              ('if', ('eq', v('x'), c(1)), ('write', c(i), c(0)), ('tm', c(0)))) for i in range(n)]
    some = ('tm', c(0))
    for i in range(n):
        some = ('let', 'y', ('read', c(i)), ('if', ('eq', v('y'), c(1)), ('tm', c(1)), some))
    return {k: 1 for k in range(KEYS)}, [some] * 3, tasks


# ---------------------------------------------------------------------------------------------
# 5. Fleets: tasks as a set of keys read and a set of keys written
# ---------------------------------------------------------------------------------------------

def fleet(rng, n, r, w, k, hot=0.0):
    """k tasks on n keys.  Each reads r keys and writes w of them.  With hot > 0 there is one
    more key, a registry: every task reads it, and a task writes it with probability `hot`.
    Returns the edges of the graph of stale reads."""
    reads, writes = [], []
    for _ in range(k):
        keys = [int(rng.random() * n) for _ in range(r)]
        while len(set(keys)) < r:               # r different keys
            keys = list(dict.fromkeys(keys + [int(rng.random() * n)]))[:r]
        reads.append(set(keys))
        writes.append(set(keys[:w]))
        if hot > 0:
            reads[-1].add(n)
            if rng.random() < hot:
                writes[-1].add(n)
    return {i: {j for j in range(k) if j != i and reads[i] & writes[j]} for i in range(k)}


def components(edges):
    """The strongly connected components with more than one vertex (Tarjan)."""
    index, low, stack, on, out, counter = {}, {}, [], set(), [], count()

    def visit(root):
        work = [(root, iter(sorted(edges[root])))]
        index[root] = low[root] = next(counter)
        stack.append(root)
        on.add(root)
        while work:
            node, it = work[-1]
            for nxt in it:
                if nxt not in index:
                    index[nxt] = low[nxt] = next(counter)
                    stack.append(nxt)
                    on.add(nxt)
                    work.append((nxt, iter(sorted(edges[nxt]))))
                    break
                if nxt in on:
                    low[node] = min(low[node], index[nxt])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[node])
                if low[node] == index[node]:
                    comp = set()
                    while True:
                        top = stack.pop()
                        on.discard(top)
                        comp.add(top)
                        if top == node:
                            break
                    if len(comp) > 1:
                        out.append(comp)

    for node in sorted(edges):
        if node not in index:
            visit(node)
    return out


def resumes(edges):
    """The number of tasks that resume if the queue takes them as they come, and an upper bound
    of the number if it takes them in a good order: in each cyclic component, repeatedly drop
    a vertex with the most edges inside and split again."""
    arrival = sum(any(j < i for j in edges[i]) for i in edges)
    dropped, work = 0, components(edges)
    while work:
        comp = work.pop()
        inner = {i: edges[i] & comp for i in comp}
        worst = max(sorted(comp), key=lambda i: len(inner[i]) + sum(i in inner[j] for j in comp))
        dropped += 1
        rest = comp - {worst}
        work.extend(components({i: inner[i] - {worst} for i in rest}))
    return arrival, dropped


def overlap(n, r, w):
    """The probability that one task has read a key that another has written."""
    return 1 - Fraction(comb(n - r, w), comb(n, w))


def expected_arrival(p, k):
    """The expected number of tasks that resume in the order of arrival."""
    return k - (1 - (1 - p) ** k) / p


# ---------------------------------------------------------------------------------------------
# 6. The import graph of a library
# ---------------------------------------------------------------------------------------------

def cones(path):
    """For every module of the graph, three sets of modules whose check reads it: under
    tracking by files, for a change of its public scope, and for a change of its private
    scope.  Returns the sizes."""
    rows = [line.rstrip('\n').split('\t') for line in open(path) if not line.startswith('#')]
    n = len(rows)
    pub, priv, alls = ([[int(x) for x in row[col].split()] for row in rows] for col in (1, 2, 3))
    every = [pub[i] + priv[i] + alls[i] for i in range(n)]

    def closure(start, step):
        seen, work = set(start), list(start)
        while work:
            for nxt in step[work.pop()]:
                if nxt not in seen:
                    seen.add(nxt)
                    work.append(nxt)
        return seen

    below = [closure(every[i], every) for i in range(n)]              # everything imported, by files
    private = [closure(alls[i], alls) for i in range(n)]              # private scopes that i sees
    public = []
    for i in range(n):                                                # public scopes that i sees
        direct = set(every[i]).union(*[every[a] for a in private[i]]) if private[i] else set(every[i])
        public.append(closure(direct, pub))
    sizes = {'file': [0] * n, 'public': [0] * n, 'private': [0] * n}
    for i in range(n):
        for name, sets in (('file', below), ('public', public), ('private', private)):
            for m in sets[i]:
                sizes[name][m] += 1
    assert all(private[i] <= public[i] | private[i] and public[i] <= below[i] for i in range(n))
    return n, (sum(map(len, pub)), sum(map(len, priv)), sum(map(len, alls))), sizes


# ---------------------------------------------------------------------------------------------
# The tests
# ---------------------------------------------------------------------------------------------

def scenario(gen, rng, k):
    base, checks = gen.repository()
    tasks = {i: gen.task() for i in range(k)}
    runs = {i: Run(base, checks, Stream(int(rng.random() * 2 ** 32))).run(tasks[i]) for i in range(k)}
    return base, checks, tasks, runs


def main(outdir):
    global BROKEN
    rng = random.Random(2026)
    gen = Gen(rng)
    lines, nums = [], {}

    # Section 2: two tasks that each keep a check, and together break it
    base, checks, tasks = skew(2)
    tasks = dict(enumerate(tasks))
    runs = {i: Run(base, checks, Stream(0)).run(tasks[i]) for i in tasks}
    union = {**base, **runs[0].over, **runs[1].over}
    assert all(Run({**base, **runs[i].over}, checks, None).perform('check', 0)[0] == 1 for i in tasks)
    assert Run(union, checks, None).perform('check', 0)[0] == 0
    assert graph(base, runs) == {0: {1}, 1: {0}} and topological(graph(base, runs)) is None
    state, new = merge(base, checks, tasks, runs, [0, 1], 0)
    assert new[0].resumed is None and new[1].resumed == 0 and new[1].over == {}
    assert state == serial(base, checks, tasks, [0, 1], new) == {**base, 0: 0}
    assert Run(state, checks, None).perform('check', 0)[0] == 1
    lines.append('the two tasks of Section 2: each keeps the check, their union breaks it, and the queue '
                 'lets the second task resume at its first read')

    # Theorem 4.2: a replay on another state is a run on that state
    moved = resumed = kept = made = keptr = 0
    for _ in range(4000):
        base, checks = gen.repository()
        task = gen.task()
        first = Run(base, checks, Stream(int(rng.random() * 2 ** 32))).run(task)
        other = {k: (gen.below(VALUES) if rng.random() < 0.3 else base[k]) for k in base}
        again = Run(other, checks, Stream(int(rng.random() * 2 ** 32)), first.J, changed(base, other)).run(task)
        live = Run(other, checks, Script(answers(again.J))).run(task)
        assert (live.J, live.over, live.value) == (again.J, again.over, again.value)
        if again.resumed is None:
            assert (plain(again.J), again.over, again.value) == (plain(first.J), first.over, first.value)
            assert again.calls == 0
        else:
            assert plain(again.J[:again.resumed]) == plain(first.J[:again.resumed])
            assert again.calls == sum(entry[0] == 'model' for entry in again.J[again.resumed:])
        if not footprint(first.J) & changed(base, other):
            assert again.again == 0 and again.resumed is None
        moved += 1
        resumed += again.resumed is not None
        kept += sum(entry[0] == 'model' for entry in again.J) - again.calls
        made += again.calls
        if again.resumed is not None:
            keptr += sum(entry[0] == 'model' for entry in again.J[:again.resumed])
    lines.append(f'4000 tasks replayed on a state that differs in some keys: every replay is the live run on '
                 f'that state with the same answers of the model; {resumed} replays resume, and they keep '
                 f'{kept} answers of the model and ask for {made}')
    nums.update(Rebases='4,000', RebaseResumed=f'{resumed:,}', RebaseKept=f'{kept:,}', RebaseMade=f'{made:,}',
                ResumedKeptPercent=f'{100 * keptr / (keptr + made):.0f}')

    # Theorem 4.3 and its corollaries: the queue is the serial execution in its order
    queues = free = cyclic = within = 0
    calls = saved = entries = repeated = untouched = compared = resumes_ = 0
    for _ in range(3000):
        k = 2 + gen.below(3)
        base, checks, tasks, runs = scenario(gen, rng, k)
        order = list(range(k))
        for i in range(k - 1, 0, -1):
            j = gen.below(i + 1)
            order[i], order[j] = order[j], order[i]
        state, new = merge(base, checks, tasks, runs, order, int(rng.random() * 2 ** 32))
        assert state == serial(base, checks, tasks, order, new)
        queues += 1
        calls += sum(run.calls for run in new.values())
        saved += sum(len(answers(run.J)) - run.calls for run in new.values())
        entries += sum(entry[0] in ('read', 'check', 'scan') for run in runs.values() for entry in run.J)
        repeated += sum(run.again for run in new.values())
        untouched += sum(run.again == 0 and run.resumed is None for run in new.values())
        compared += sum(run.again > 0 and run.resumed is None for run in new.values())
        resumes_ += sum(run.resumed is not None for run in new.values())
        # Corollary 4.5: an order along the edges costs nothing
        edges = graph(base, runs)
        good = topological(edges)           # a task before every task whose writes it has read
        if good is not None:
            free += 1
            state, new = merge(base, checks, tasks, runs, good, 0)
            assert all((run.again, run.calls, run.resumed) == (0, 0, None) for run in new.values())
            assert all((new[i].J, new[i].over) == (runs[i].J, runs[i].over) for i in runs)
            union = dict(base)
            for i in good:
                union.update(runs[i].over)
            assert state == union == serial(base, checks, tasks, good, new)
        else:
            cyclic += 1
            # Corollary 4.6: the tasks outside a feedback set first, along the edges
            drop = feedback(edges)
            rest = topological({i: edges[i] - drop for i in edges if i not in drop})
            state, new = merge(base, checks, tasks, runs, rest + sorted(drop), int(rng.random() * 2 ** 32))
            assert all(new[i].resumed is None and new[i].again == 0 for i in rest)
            assert state == serial(base, checks, tasks, rest + sorted(drop), new)
            within += sum(new[i].resumed is not None for i in drop) <= len(drop)
    assert within == cyclic
    lines.append(f'{queues} queues of two to four tasks in a random order: the final state is that of the tasks '
                 f'run one after the other with the same answers; the queues ask the model {calls} times and '
                 f'keep {saved} answers, and make {repeated} of {entries} reads and checks again; {free} '
                 f'sets of tasks have no cycle and merge along their edges with nothing made again, and in '
                 f'the other {cyclic} only tasks of a smallest feedback set can resume')
    nums.update(Queues=f'{queues:,}', QueueCalls=f'{calls:,}', QueueSaved=f'{saved:,}',
                SavedPercent=f'{100 * saved / (saved + calls):.0f}', Entries=f'{entries:,}',
                Repeated=f'{repeated:,}', RepeatedPercent=f'{100 * repeated / entries:.0f}',
                Free=f'{free:,}', Cyclic=f'{cyclic:,}', Untouched=f'{untouched:,}', Compared=f'{compared:,}',
                Resumed=f'{resumes_:,}', QueueTasks=f'{untouched + compared + resumes_:,}')

    # Corollary 4.8: tasks that end with the suite of checks
    for _ in range(1000):
        k = 2 + gen.below(3)
        base, checks = gen.repository()
        tasks = {i: with_suite(gen.task()) for i in range(k)}
        runs = {i: Run(base, checks, Stream(int(rng.random() * 2 ** 32))).run(tasks[i]) for i in range(k)}
        state, new = merge(base, checks, tasks, runs, list(range(k)), int(rng.random() * 2 ** 32))
        last = new[k - 1].J[-3:]
        assert [entry[:2] for entry in last] == [('check', 0), ('check', 1), ('check', 2)]
        assert [entry[2] for entry in last] == [Run(state, checks, None).perform('check', i)[0] for i in range(3)]
    lines.append('1000 queues of tasks that end with the three checks: the verdicts in the journal of the '
                 'last task are the values of the checks in the merged state')

    # Proposition 4.7: with a cycle, the union of the writes need not be any serial outcome
    for n in (2, 3, 4):
        base, checks, tasks = skew(n)
        tasks = dict(enumerate(tasks))
        runs = {i: Run(base, checks, Stream(0)).run(tasks[i]) for i in tasks}
        union = dict(base)
        for i in tasks:
            union.update(runs[i].over)
        outcomes = []
        for order in permutations(range(n)):
            state = dict(base)
            for i in order:
                state.update(Run(state, checks, Stream(0)).run(tasks[i]).over)
            outcomes.append(state)
        assert union not in outcomes and topological(graph(base, runs)) is None
        assert all(Run(state, checks, None).perform('check', 0)[0] == 1 for state in outcomes)
    lines.append('rings of two, three and four tasks: the union of their writes is the outcome of no order, '
                 'and it breaks a check that every order keeps')

    # every step of the replay is needed
    tries = {}
    for step in STEPS:
        BROKEN = step
        for i in range(1, 100001):
            k = 2 + gen.below(2)
            base, checks, tasks, runs = scenario(gen, rng, k)
            state, new = merge(base, checks, tasks, runs, list(range(k)), int(rng.random() * 2 ** 32))
            BROKEN = None
            wrong = state != serial(base, checks, tasks, list(range(k)), new)
            BROKEN = step
            if wrong:
                tries[step] = i
                break
        BROKEN = None
    assert set(tries) == set(STEPS), tries
    lines.append(f'{len(STEPS)} queues with one broken step each: every one ends in a state that is not the '
                 'serial outcome, after ' + ', '.join(f'{s} {n}' for s, n in tries.items()) + ' sets of tasks')
    nums.update(Steps=str(len(STEPS)))
    for step, n in tries.items():
        nums['Step' + ''.join(part.capitalize() for part in step.split('-'))] = f'{n:,}'

    # Section 5: fleets
    n, r, w = 10000, 50, 5
    p = overlap(n, r, w)
    nums['FleetP'] = f'{100 * float(p):.1f}'
    assert abs(float(p) - r * w / n) < 0.001
    rows = []
    for k in (10, 20, 40, 80, 160):
        arrive = best = cyc = 0
        samples = 300
        for _ in range(samples):
            edges = fleet(rng, n, r, w, k)
            a, b = resumes(edges)
            arrive, best, cyc = arrive + a, best + b, cyc + (b > 0)
        exact = float(expected_arrival(p, k))
        assert abs(arrive / samples - exact) < 0.05 * exact + 0.1
        rows.append((k, exact, arrive / samples, best / samples, cyc / samples))
        tag = {10: 'a', 20: 'b', 40: 'c', 80: 'd', 160: 'e'}[k]
        nums['FleetKp' + tag] = f'{float(k * p):.2f}'
        nums['FleetArrive' + tag] = f'{exact:.1f}'
        nums['FleetBest' + tag] = f'{best / samples:.2f}'
        nums['FleetCyclic' + tag] = f'{100 * cyc / samples:.0f}'
    lines.append(f'fleets on {n} keys, {r} read and {w} written by each task (overlap {float(p):.4f}), 300 '
                 f'samples each: tasks that resume in the order of arrival and in a good order: '
                 + '; '.join(f'k={k}: {a:.2f} and {b:.2f}' for k, _, a, b, _ in rows)
                 + '; the closed form for the order of arrival agrees within five percent')
    # pairs of tasks that have read each other's writes
    mutual, pairs = 0, 200000
    for _ in range(pairs):
        edges = fleet(rng, n, r, w, 2)
        mutual += bool(edges[0] and edges[1])
    estimate = float(Fraction(w * w, n) + p * p)
    assert abs(mutual / pairs - estimate) < 0.15 * estimate
    nums['FleetMutual'] = f'{100 * mutual / pairs:.2f}'
    nums['FleetRatio'] = f'{float(p) / (mutual / pairs):.0f}'
    # the fleet that finishes most tasks per unit of time, if an affected task costs half a task
    nums['FleetSizeArrive'] = f'{(2 / (0.5 * float(p))) ** 0.5:.0f}'
    nums['FleetSizeEdges'] = f'{(2 / (0.5 * estimate)) ** 0.5:.0f}'
    # a registry that every task reads and one task in ten writes
    hots = []
    for k in (10, 20, 40):
        best = 0
        for _ in range(300):
            best += resumes(fleet(rng, n, r, w, k, hot=0.1))[1]
        hots.append((k, best / 300))
        nums['FleetHot' + {10: 'a', 20: 'b', 40: 'c'}[k]] = f'{best / 300:.2f}'
        assert best / 300 >= 0.1 * k - 1
    lines.append(f'{pairs} pairs of tasks: in {mutual} each has read a write of the other, against the estimate '
                 f'{estimate:.5f}; with a registry that every task reads and one in ten writes, tasks that '
                 f'resume in a good order: ' + '; '.join(f'k={k}: {b:.2f}' for k, b in hots))

    # Section 6: the import graph of Lean's library
    here = os.path.dirname(os.path.abspath(__file__))
    modules, (pubs, privs, alls), sizes = cones(os.path.join(here, 'lean-imports.txt'))
    stats = {}
    for name, xs in sizes.items():
        xs = sorted(xs)
        stats[name] = (sum(xs) / modules, xs[modules // 2], xs[-1], sum(xs) / modules ** 2)
    assert stats['private'][0] <= stats['public'][0] <= stats['file'][0]
    lines.append(f'the import graph of Lean: {modules} modules, {pubs} public imports, {privs} plain imports, '
                 f'{alls} imports of a private scope; modules that must be checked again after a change of '
                 f'one module, as mean, median and largest: '
                 + '; '.join(f'{name} {m:.1f}, {med}, {top}' for name, (m, med, top, _) in stats.items()))
    nums.update(Modules=f'{modules:,}', ImportsPublic=f'{pubs:,}', ImportsPlain=f'{privs:,}',
                ImportsAll=f'{alls:,}',
                ConePrivateNone=f'{100 * sum(x == 0 for x in sizes["private"]) / modules:.0f}',
                ConePublicHalf=f'{sum(2 * x >= modules for x in sizes["public"]):,}',
                ConeFileHalf=f'{sum(2 * x >= modules for x in sizes["file"]):,}')
    for name, (mean, med, top, prob) in stats.items():
        tag = name.capitalize()
        nums.update({'Cone' + tag + 'Mean': f'{mean:,.1f}', 'Cone' + tag + 'Median': f'{med:,}',
                     'Cone' + tag + 'Max': f'{top:,}', 'Cone' + tag + 'P': f'{100 * prob:.2f}',
                     'Cone' + tag + 'Fleet': f'{1 / prob:,.0f}'})

    with open(f'{outdir}/check.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    with open(f'{outdir}/numbers.tex', 'w') as f:
        f.write('% written by merge.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
