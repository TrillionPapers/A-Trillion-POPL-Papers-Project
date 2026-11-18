#!/usr/bin/env python3
"""Tests the claims of "An Injection Outlives Its Text" on an implementation of its machine.

The file has four parts.

1. The machine: contexts and stores with labels, the model, and the five ways to compact.
2. Running a program honestly, and under attack with every choice of the attacker.
3. The task of Section 5 and the simulation of Section 9.
4. The tests.  `python3 outlives.py out` writes out/check.txt, out/numbers.tex and the tables.

A test is not a proof.  The proofs are in the paper.
"""
import os
import random
import sys
import zlib
from itertools import count, product

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. An entry is a pair (label, content).  The labels are ordered: trusted below typed below
#    untrusted.  The label of a context is the highest label of its entries.
# ---------------------------------------------------------------------------------------------

T, V, U = 0, 1, 2
OUTPUTS = ('a', 'b', 'c')           # what the model can ask for in one step
SENSITIVE = ('c',)                  # the outputs for which a tainted context needs approval
DATA = (0, 1, 2)                    # what an honest untrusted source can say
EVIL = ('x',)                       # a text that no honest source would show
SUMMARIES = (('evil', 0), ('evil', 1))      # summaries that an attacker may have the model write
NOTES = (0, 1)                      # what the model can write to a cell of the store


def level(ctx):
    """The label of a context: what the harness believes about it."""
    return max((e[0] for e in ctx), default=T)


def truth(ctx):
    """What a context is: untrusted if it holds a text that the attacker controls.  In the
    machine of the paper the label and the truth are the same.  A mistake of Section 6 gives
    an entry a better label than it deserves, and then they differ."""
    return max((true for _, true, _ in ctx), default=T)


def pick(kind, ctx, size):
    """The honest model: a fixed function of what it reads.  `kind` separates its uses."""
    return zlib.crc32(repr((kind, tuple(c for _, _, c in ctx))).encode()) % size


class Machine:
    """One run.  An entry is (label, truth, content).  `choose(what, options, honest)` decides
    everything that is not determined: what an untrusted source shows, and, when the context
    is in truth untrusted, what the model does."""

    def __init__(self, choose, ledger=0):
        self.choose, self.ctx, self.store, self.events = choose, (), {}, []
        self.ledger, self.state = ledger, 0      # a monitor with `ledger` states, kept by the harness

    def model(self, what, options, honest):
        """The model answers honestly unless its context is untrusted."""
        if truth(self.ctx) == U:
            return self.choose(what, options, honest)
        return honest

    def do(self, op):
        ctx, kind = self.ctx, op[0]
        if kind == 'say':
            self.ctx += ((T, T, op[1]),)
        elif kind == 'read':
            self.ctx += ((U, U, self.choose('source', DATA + EVIL, None)),)
        elif kind == 'step':
            out = self.model('output', OUTPUTS, OUTPUTS[pick('step', ctx, len(OUTPUTS))])
            self.events.append(('out', level(ctx), out))
            if self.ledger:
                self.state = (self.state + 1 + OUTPUTS.index(out)) % self.ledger
            self.ctx += ((T if MUTANT == 'wash-record' else level(ctx), truth(ctx), ('did', out)),)
        elif kind == 'save':
            note = self.model('note', NOTES, NOTES[pick('save', ctx, len(NOTES))])
            self.store[op[1]] = (T if MUTANT == 'wash-store' else level(ctx), truth(ctx), note)
        elif kind == 'savev':                    # a note that is a value of a type with op[2] values
            value = self.model('value', tuple(range(op[2])), pick('savev', ctx, op[2]))
            kept = self.keep(ctx)
            self.store[op[1]] = (max(V, level(kept)), max(V, truth(kept)), ('val', value))
        elif kind == 'fresh':                    # a new session: the context is empty, the store stays
            self.ctx = ()
        elif kind == 'load':
            self.ctx += (self.store.get(op[1], (T, T, None)),)
        elif kind == 'compact':
            self.compact(*op[1:])
        else:
            raise ValueError(op)

    @staticmethod
    def keep(ctx):
        """What a clean compaction keeps: the entries that the harness does not label untrusted."""
        if MUTANT == 'relabel':
            return tuple((T, true, c) for _, true, c in ctx)
        return tuple(e for e in ctx if e[0] != U)

    def compact(self, how, size=1):
        """Section 3.  `free`: the model writes a summary, which has the label of the context.
        `clean`: the entries that are not untrusted stay.  `typed`: as clean, with one value of
        a type of `size` values that the model extracts.  With a ledger, its state is added:
        a value of a type with as many values as the ledger has states."""
        ctx = self.ctx
        if how == 'none':
            return
        if how == 'free':
            summary = self.model('summary', (('sum', ctx),) + SUMMARIES, ('sum', ctx))
            self.ctx = ((T if MUTANT == 'wash-summary' else level(ctx), truth(ctx), summary),)
        else:
            kept = self.keep(ctx)
            if how == 'typed':
                options = tuple(range(size)) + (SUMMARIES if MUTANT == 'typed-text' else ())
                value = self.model('value', options, pick('typed', ctx, size))
                kept += ((V, U if value in SUMMARIES else V, ('val', value)),)
            self.ctx = kept
        if self.ledger:
            self.ctx += ((V, V, ('ledger', self.state)),)

    def seen(self):
        """What happens without anybody being asked: the outputs of contexts that are not
        labelled untrusted, and the cells of the store that are not."""
        outs = tuple((label, out) for _, label, out in self.events if label != U)
        cells = tuple(sorted((c, v) for c, (label, _, v) in self.store.items() if label != U))
        return outs, cells

    def asks(self):
        return sum(label == U and out in SENSITIVE for _, label, out in self.events)


# ---------------------------------------------------------------------------------------------
# 2. Runs.
# ---------------------------------------------------------------------------------------------

def run(program, choices, ledger=0):
    """One run in which the attacker makes the given choices, in order.  A choice of None is
    the honest one.  Returns the machine and the number of choices that were used."""
    it = iter(choices)
    used = [0]

    def choose(what, options, honest):
        used[0] += 1
        c = next(it)
        return honest if c is None else c

    m = Machine(choose, ledger)
    for op in program:
        m.do(op)
    return m, used[0]


def attacks(program, ledger=0):
    """Every run under attack: the machines, one for every sequence of choices."""
    out, todo = [], [()]
    while todo:
        prefix = todo.pop()
        options = [None]

        def choose(what, opts, honest, prefix=prefix, state={'n': 0}):
            raise RuntimeError

        # run with the prefix, and find the options at the first choice beyond it
        pending = []
        it = iter(prefix)

        def choose(what, opts, honest):
            try:
                return next(it)
            except StopIteration:
                pending.append(opts)
                raise Stop

        m = Machine(choose, ledger)
        try:
            for op in program:
                m.do(op)
            out.append(m)
        except Stop:
            todo += [prefix + (o,) for o in pending[0]]
    return out


class Stop(Exception):
    pass


def honest(program, data, ledger=0):
    """The run in which the untrusted sources show `data`, in order, and the model is honest."""
    it = iter(data)

    def choose(what, options, honest_):
        return next(it) if what == 'source' else honest_

    m = Machine(choose, ledger)
    for op in program:
        m.do(op)
    return m


def reads(program):
    return sum(op[0] == 'read' for op in program)


def capacity(program, ledger=0):
    """Theorem 4.3: the product of the sizes of the types of the values that cross a
    compaction, among them the state of the ledger."""
    n = 1
    for op in program:
        if op[0] == 'compact' and op[1] != 'none':
            n *= (op[2] if op[1] == 'typed' else 1) * (ledger or 1)
        elif op[0] == 'savev':
            n *= op[2]
    return n


# ---------------------------------------------------------------------------------------------
# 3. The task of Section 5: the agent reads a datum and must then act on its class, several
#    times.  The model of the task is honest in a particular way: it looks for the class.
# ---------------------------------------------------------------------------------------------

class Task:
    """`steps` outputs after a compaction, each of which should name the class of the datum
    that was read before it.  The data are 0..size-1 and the class of d is d % classes."""

    def __init__(self, size, classes, steps):
        self.size, self.classes, self.steps = size, classes, steps

    def answer(self, ctx):
        """What the model of the task says for a context: the class of the last thing it knows."""
        for label, content in reversed(ctx):
            if label == U and isinstance(content, int):
                return content % self.classes
            if label == V and content[0] == 'val':
                return content[1]
            if content and isinstance(content, tuple) and content[0] == 'sum':
                return self.answer(content[1])
        return 0

    def futures(self, how):
        """The sequences of outputs after the compaction: for every honest datum, and under
        attack.  Under attack the source shows anything, and the model, while its context is
        untrusted, says anything."""
        size = self.classes
        honest_, attack = {}, set()
        for d in range(self.size):
            ctx = self.compacted(((T, 'task'), (U, d)), how, None)
            honest_[d] = tuple(self.answer(ctx) for _ in range(self.steps))
        firsts = [((T, 'task'), (U, d)) for d in list(range(self.size)) + ['x']]
        for before in firsts:
            for choice in [None] + list(range(size)) + list(SUMMARIES):
                ctx = self.compacted(before, how, choice)
                if ctx is None:
                    continue
                if level(ctx) == U:
                    attack |= set(product(range(self.classes), repeat=self.steps))
                else:
                    attack.add(tuple(self.answer(ctx) for _ in range(self.steps)))
        return honest_, attack

    def compacted(self, ctx, how, choice):
        """The context after the compaction.  `choice` is what the attacker has the model write,
        or None for the honest summary or value.  None if the choice does not fit."""
        if how == 'none':
            return ctx if choice is None else None
        if how == 'free':
            if choice is not None and choice not in SUMMARIES:
                return None
            return ((U, ('sum', ctx) if choice is None else choice),)
        kept = tuple(e for e in ctx if e[0] != U)
        if how == 'clean':
            return kept if choice is None else None
        if choice is not None and choice not in range(self.classes):
            return None
        value = self.answer(ctx) if choice is None else choice
        return kept + ((V, ('val', value)),)


# ---------------------------------------------------------------------------------------------
# 4. The tests.
# ---------------------------------------------------------------------------------------------

def random_program(rng, typed=True, length=7):
    ops = [('say', 'task')]
    for _ in range(1 + int(rng.random() * length)):
        x = rng.random()
        if x < 0.16:
            ops.append(('read',))
        elif x < 0.50:
            ops.append(('step',))
        elif x < 0.57:
            ops.append(('save', int(rng.random() * 2)))
        elif x < 0.60 and typed:
            ops.append(('savev', int(rng.random() * 2), 2))
        elif x < 0.70:
            ops.append(('load', int(rng.random() * 2)))
        elif x < 0.76:
            ops.append(('say', int(rng.random() * 3)))
        elif x < 0.84:
            ops.append(('compact', 'free'))
        elif x < 0.92 or not typed:
            ops.append(('compact', 'clean'))
        else:
            ops.append(('compact', 'typed', 2 + int(rng.random() * 2)))
    return tuple(ops)


def trial(rng, counts, typed):
    """Theorems 4.2 and 4.3 on one random program: without a typed value, what is seen is the
    same in every run under attack; in general the number of things that can be seen is at
    most the capacity; and every honest run is one of the runs under attack."""
    program = random_program(rng, typed)
    ledger = 0 if rng.random() < 0.6 or not typed else 2 + int(rng.random() * 2)
    runs = attacks(program, ledger)
    seen = {m.seen() for m in runs}
    cap = capacity(program, ledger)
    assert len(seen) <= cap, (program, ledger, len(seen), cap)
    for data in product(DATA, repeat=reads(program)):
        assert honest(program, data, ledger).seen() in seen
    # Lemma 3.2: after an untrusted entry and before the next compaction, every output is untrusted
    for m in runs[:1]:
        tainted = False
        events = iter(m.events)
        for op in program:
            if op[0] == 'read':
                tainted = True
            elif op[0] == 'compact' and op[1] in ('clean', 'typed'):
                tainted = False
            elif op[0] == 'step':
                label = next(events)[1]
                assert not tainted or label == U
    counts['programs'] += 1
    counts['runs'] += len(runs)
    counts['one'] += cap == 1
    counts['full'] += len(seen) == cap and cap > 1
    counts['more'] += cap > 1


MUTANTS = ('wash-summary', 'wash-record', 'wash-store', 'relabel', 'typed-text')


def catches(name):
    global MUTANT
    MUTANT = name
    rng, counts = random.Random(2026), dict.fromkeys(('programs', 'runs', 'one', 'full', 'more'), 0)
    try:
        for i in range(1, 4001):
            trial(rng, counts, typed=True)
        return None
    except AssertionError:
        return counts['programs'] + 1
    finally:
        MUTANT = None


def discipline(rng, how, sessions=200, length=12):
    """Section 9: a long run in which the agent reads an untrusted source now and then.  After
    every read the context is compacted in the given way, or never.  Counts the questions to
    the user under attack in the worst case, which is one for every sensitive output of an
    untrusted context, and the steps at which the attacker chooses the output."""
    asks = chosen = steps = 0
    for _ in range(sessions):
        tainted = False
        for _ in range(length):
            if rng.random() < 0.15:
                tainted = True
                if how in ('clean', 'typed'):
                    tainted = False             # the compaction follows the read at once
            else:
                steps += 1
                if tainted:
                    chosen += 1
                    asks += 1                   # worst case: the attacker asks for a sensitive output
    return steps, chosen, asks


def main(outdir):
    global MUTANT
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten']

    # Theorems 4.2 and 4.3
    plain = dict.fromkeys(('programs', 'runs', 'one', 'full', 'more'), 0)
    for _ in range(3000):
        trial(rng, plain, typed=False)
    claim('same', plain['one'] == plain['programs'])
    typed = dict.fromkeys(('programs', 'runs', 'one', 'full', 'more'), 0)
    for _ in range(3000):
        trial(rng, typed, typed=True)
    claim('capacity', typed['more'] > 0 and typed['full'] > 0)
    lines.append(f"{plain['programs']} programs without typed values, {plain['runs']} runs under attack: what is seen "
                 'without asking is the same in all runs of a program')
    lines.append(f"{typed['programs']} programs with typed values and ledgers, {typed['runs']} runs under attack: the "
                 f"number of things seen is at most the capacity; the capacity is more than one for {typed['more']} "
                 f"programs and is reached by {typed['full']} of them")
    nums.update(Programs=f"{plain['programs']:,}", PlainRuns=f"{plain['runs']:,}", TypedRuns=f"{typed['runs']:,}",
                TypedMore=f"{typed['more']:,}", TypedFull=f"{typed['full']:,}")

    # every program of at most four operations after the task is stated
    alphabet = (('read',), ('step',), ('save', 0), ('savev', 0, 2), ('load', 0), ('compact', 'free'),
                ('compact', 'clean'), ('compact', 'typed', 2), ('fresh',))
    short = dict(programs=0, runs=0)
    for n in range(1, 5):
        for ops in product(alphabet, repeat=n):
            program = (('say', 'task'),) + ops
            runs = attacks(program)
            assert len({m.seen() for m in runs}) <= capacity(program), program
            short['programs'] += 1
            short['runs'] += len(runs)
    claim('short', True)
    lines.append(f"every program of at most four of {len(alphabet)} operations: {short['programs']} programs, "
                 f"{short['runs']} runs under attack, the number of things seen is at most the capacity")
    nums.update(ShortPrograms=f"{short['programs']:,}", ShortRuns=f"{short['runs']:,}", ShortOps=spelled[len(alphabet)])

    # Section 4: two sessions and a note
    rows = []
    for name, note, mutant in (('a note in free text', ('save', 0), None),
                               ('the same, taken for trusted', ('save', 0), 'wash-store'),
                               ('a note of a type with two values', ('savev', 0, 2), None)):
        MUTANT = mutant
        program = (('say', 'task'), ('read',), note, ('fresh',), ('say', 'next task'), ('load', 0), ('step',), ('step',))
        runs = attacks(program)
        MUTANT = None
        futures = {tuple(out for _, _, out in m.events) for m in runs}
        unasked = {tuple(out for _, label, out in m.events if label != U) for m in runs}
        asked = max(sum(label == U for _, label, _ in m.events) for m in runs)
        lines.append(f'two sessions, {name}: {len(futures)} futures of the second session, {len(unasked)} of them '
                     f'without asking, up to {asked} questions')
        rows.append((name, len(futures), len(unasked), asked))
    tables['memory'] = [f'{name} & {a} & {b} & {c} \\\\' for name, a, b, c in rows]
    claim('memory', [r[1:] for r in rows] == [(9, 1, 2), (9, 9, 0), (2, 2, 0)])

    # Proposition 7.1: how long a context stays untrusted between compactions
    rows, worst = [], 0.0
    for p in (0.05, 0.1, 0.2):
        for k in (5, 20, 80):
            q = 1 - p
            formula = 1 - (1 - q ** k) / (k * (1 - q))
            sim, total, tainted = random.Random(2026), 0, 0
            for _ in range(20000):
                dirty = False
                for _ in range(k):
                    total += 1
                    tainted += dirty
                    dirty = dirty or sim.random() < p
            worst = max(worst, abs(tainted / total - formula))
            rows.append(f'{p} & {k} & {100 * formula:.0f} & {100 * tainted / total:.0f} \\\\')
            lines.append(f'reads with probability {p}, a clean compaction every {k} operations: '
                         f'{100 * formula:.1f} percent untrusted by the formula, {100 * tainted / total:.1f} simulated')
    tables['decay'] = rows
    claim('decay', worst < 0.01)
    nums['DecayPeriods'] = '20,000'

    # Section 2: the example
    # the task of the example is the first for which the model acts differently on each of three values
    for i in count():
        example = (('say', 'task %d' % i), ('read',), ('step',), ('compact', 'typed', 3), ('step',), ('step',))
        if len({tuple(out for _, _, out in m.events[1:]) for m in attacks(example)}) == 3:
            break
    names = {'none': 'no compaction', 'free': 'a summary in free text', 'washed': 'the same, taken for trusted',
             'clean': 'the trusted entries', 'typed': 'the trusted entries and a value of three'}
    rows = []
    for how, size in (('none', 1), ('free', 1), ('washed', 1), ('clean', 1), ('typed', 3)):
        MUTANT = 'wash-summary' if how == 'washed' else None
        kind = 'free' if how == 'washed' else how
        program = example[:3] + ((('compact', kind, size) if how == 'typed' else ('compact', kind)),) + example[4:]
        runs = attacks(program)
        MUTANT = None
        after = {tuple(out for _, _, out in m.events[1:]) for m in runs}
        unasked = {tuple(out for _, label, out in m.events[1:] if label != U) for m in runs}
        asked = max(sum(label == U for _, label, _ in m.events[1:]) for m in runs)
        lines.append(f'example, {how}: {len(runs)} runs under attack, {len(after)} futures after the compaction, '
                     f'{len(unasked)} without asking, up to {asked} questions')
        rows.append((how, len(after), len(unasked), asked))
    claim('example', [r[1:] for r in rows] == [(9, 1, 2), (9, 1, 2), (9, 9, 0), (1, 1, 0), (3, 3, 0)])
    tables['example'] = [f'{names[how]} & {a} & {u} & {q} \\\\' for how, a, u, q in rows]

    # laundering: each channel, with its label dropped
    found = {name: catches(name) for name in MUTANTS}
    claim('laundering', all(found.values()))
    lines.append('labels dropped, and the number of random programs until what is seen differs between attacks or '
                 'exceeds the capacity: ' + ', '.join(f'{k} {v}' for k, v in found.items()))
    nums.update(Mutants=spelled[len(MUTANTS)], TryLeast=str(min(found.values())), TryMost=str(max(found.values())),
                ProgramsAll=f"{plain['programs'] + typed['programs']:,}")
    for name, n in found.items():
        nums['Try' + ''.join(part.capitalize() for part in name.split('-'))] = str(n)

    # Theorem 5.2: the task
    rows, ok = [], True
    for size, classes in ((4, 1), (4, 2), (6, 3), (6, 6)):
        task = Task(size, classes, steps=2)
        need = len({task.futures('none')[0][d] for d in range(size)})
        for how in ('free', 'clean', 'typed'):
            honest_, attack = task.futures(how)
            faithful = honest_ == task.futures('none')[0]
            ok &= (not faithful or len(attack) >= need) and set(honest_.values()) <= attack
            if how == 'typed':
                ok &= faithful and attack == set(honest_.values()) and len(attack) == need
            if how == 'clean':
                ok &= faithful == (need == 1)
            if how == 'free':
                ok &= faithful and len(attack) == classes ** 2
            lines.append(f'task with {size} data in {classes} classes, {how}: faithful {faithful}, '
                         f'{len(attack)} futures under attack, {need} needed')
            rows.append(f"{size} & {classes} & {how} & {'yes' if faithful else 'no'} & {need} & {len(attack)} \\\\")
    tables['task'] = rows
    claim('task', ok)

    # Section 9: what the disciplines cost
    rows = []
    for how in ('none', 'free', 'clean', 'typed'):
        steps, chosen, asks = discipline(random.Random(2026), how)
        lines.append(f'{how}: {steps} steps, {chosen} of them chosen by the attacker, {asks} questions at worst')
        rows.append((how, steps, chosen, asks))
    claim('cost', rows[0][2:] == rows[1][2:] and rows[2][2:] == rows[3][2:] == (0, 0) and rows[0][2] > 0)
    nums.update(CostSteps=f'{rows[0][1]:,}', CostChosen=f'{rows[0][2]:,}', CostSessions='200', CostLength='12',
                CostShare=str(round(100 * rows[0][2] / rows[0][1])))

    # Section 8: the session
    trace = [line.strip() for line in open(os.path.join(here, 'session.txt')) if line.strip()]
    calls = [x for x in trace if x not in ('compact', 'end')]
    kinds = {k: sum(x == k for x in calls) for k in ('read lookup', 'read page', 'read agent', 'act', 'step')}
    n_reads = sum(x.startswith('read') for x in calls)
    first = next(i for i, x in enumerate(calls) if x.startswith('read')) + 1
    after = [x for x in calls[first:] if not x.startswith('read')]
    kept = dropped = quiet = 0                  # outward actions: asked, with labels kept or dropped at a summary
    tainted_kept = tainted_dropped = False
    for x in trace:
        if x.startswith('read'):
            tainted_kept = tainted_dropped = True
        elif x == 'compact':
            tainted_dropped = False
        elif x == 'act':
            kept += tainted_kept
            dropped += tainted_dropped
            quiet += tainted_kept and not tainted_dropped
    lines.append(f"session: {len(calls)} calls, {n_reads} of them reads from outside ({kinds['read lookup']} lookups, "
                 f"{kinds['read page']} pages, {kinds['read agent']} reports of sub-agents), {kinds['act']} outward "
                 f"actions, {trace.count('compact')} summaries; the first read is call {first}; {len(after)} later "
                 f"calls are made by an untrusted context when labels are kept, {kept} outward actions among them; "
                 f"when a summary drops the label, {dropped} outward actions are asked about and {quiet} are not")
    claim('session', kept == kinds['act'] == dropped and quiet == 0)

    # the stretches between the summaries
    rows, stretch, number = [], [], 0
    for x in trace + ['compact']:
        if x == 'compact':
            if stretch:
                number += 1
                r = [i for i, y in enumerate(stretch) if y.startswith('read')]
                acts = [i for i, y in enumerate(stretch) if y == 'act']
                assert r and all(i > r[0] for i in acts)
                rows.append(f"{number} & {len(stretch)} & {len(r)} & {len(acts)} & {r[0] + 1 if r else '--'} & "
                            f"{sum(i > r[0] for i in acts) if r else 0} \\\\")
                lines.append(f'stretch {number}: {len(stretch)} calls, {len(r)} reads, {len(acts)} acts, first read at '
                             f"{r[0] + 1 if r else '-'}, {sum(i > r[0] for i in acts) if r else 0} acts after it")
            stretch = []
        elif x != 'end':
            stretch.append(x)
    tables['stretches'] = rows
    claim('stretches', len(rows) == 3)

    # Proposition 7.2: an injection that stays in the context is tried again at every step
    eps, sim = 0.01, random.Random(2026)
    whole, five = 1 - (1 - eps) ** len(after), 1 - (1 - eps) ** 5
    hit = sum(any(sim.random() < eps for _ in range(len(after))) for _ in range(4000)) / 4000
    claim('retried', abs(hit - whole) < 0.01 and whole > 0.95 and five < 0.05)
    lines.append(f'an injection that takes over one step in a hundred: {100 * whole:.1f} percent to take over one of '
                 f'{len(after)} steps ({100 * hit:.1f} simulated), {100 * five:.1f} percent for one of five')
    nums.update(RetryWhole=f'{100 * whole:.0f}', RetryFive=f'{100 * five:.0f}', RetryTrials='4,000',
                LookupFutures=f'{2 ** kinds["read lookup"]:,}')
    nums.update(SessionCalls=str(len(calls)), SessionReads=str(n_reads), SessionLookups=str(kinds['read lookup']),
                SessionPages=str(kinds['read page']), SessionAgents=spelled[kinds['read agent']],
                SessionActs=str(kinds['act']),
                SessionFirst=['first', 'second', 'third', 'fourth', 'fifth', 'sixth', 'seventh', 'eighth', 'ninth'][first - 1],
                SessionAfter=str(len(after)),
                SessionShare=str(round(100 * len(after) / len(calls))),
                SessionSummaries=spelled[trace.count('compact')])

    nums.update(Lines=f"{round(len(open(os.path.join(here, 'outlives.py')).readlines()), -2):,}", Seed='2026',
                Outputs=spelled[len(OUTPUTS)])
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
        f.write('% written by outlives.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by outlives.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
