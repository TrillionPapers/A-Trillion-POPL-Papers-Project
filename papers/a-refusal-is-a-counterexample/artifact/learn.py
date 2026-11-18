#!/usr/bin/env python3
"""Tests the claims of "A Refusal Is a Counterexample" on an implementation of its protocol.

The file has five parts.

1. Policies: prefix-closed regular languages as automata, with a user who answers three
   kinds of questions and counts them.
2. The learner: an observation table in the manner of Angluin.  A counterexample adds one
   experiment, found by binary search, or, in the plain variant, all of its endings.
3. The agent that learns as it works, with or without the closing question, and three agents
   that do not learn.
4. Policies of several shapes, and random ones.
5. The tests.  `python3 learn.py out` writes out/check.txt, out/numbers.tex and the tables.

A test is not a proof.  The proofs are in the paper.
"""
import os
import random
import sys
from collections import deque

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. A policy is a deterministic automaton over the actions: a start state, a table of
#    transitions, and the convention that a missing transition is a refusal.  Its language,
#    the histories that the user allows, is closed under beginnings.  A plan is the same thing.
# ---------------------------------------------------------------------------------------------

class Policy:
    def __init__(self, sigma, start, delta):
        self.sigma, self.start, self.delta = tuple(sigma), start, dict(delta)

    def run(self, w):
        """The state after the word, or None if the word is refused."""
        q = self.start
        for a in w:
            q = self.delta.get((q, a))
            if q is None:
                return None
        return q

    def allows(self, w):
        return self.run(w) is not None

    def states(self):
        seen, todo = {self.start}, [self.start]
        while todo:
            q = todo.pop()
            for a in self.sigma:
                t = self.delta.get((q, a))
                if t is not None and t not in seen:
                    seen.add(t)
                    todo.append(t)
        return seen

    def size(self):
        """The number of states of the least automaton for the language, the refusing state
        included when some word is refused."""
        states = sorted(self.states(), key=repr) + [None]
        block = {q: 0 if q is not None else 1 for q in states}
        while True:
            sig = {q: (block[q],) + tuple(block[self.delta.get((q, a))] if q is not None else 1
                                           for a in self.sigma) for q in states}
            names = {s: i for i, s in enumerate(sorted(set(sig.values())))}
            new = {q: names[sig[q]] for q in states}
            if len(set(new.values())) == len(set(block.values())):
                break
            block = new
        refused = any(self.delta.get((q, a)) is None for q in self.states() for a in self.sigma)
        return len(set(block[q] for q in states if q is not None)) + (1 if refused else 0)

    def beyond(self, other):
        """A shortest word that this automaton allows and the other refuses, or None.  This is
        how the user of the script finds what is wrong with a plan."""
        seen, todo = {(self.start, other.start)}, deque([((), self.start, other.start)])
        while todo:
            w, p, q = todo.popleft()
            for a in self.sigma:
                p2 = self.delta.get((p, a))
                if p2 is None:
                    continue
                q2 = other.delta.get((q, a)) if q is not None else None
                if q2 is None and MUTANT != 'careless-user':
                    return w + (a,)
                if (p2, q2) not in seen:
                    seen.add((p2, q2))
                    todo.append((w + (a,), p2, q2))
        return None

    def task(self, rng, length):
        """A random word that the policy allows."""
        w, q = (), self.start
        for _ in range(length):
            nexts = [a for a in self.sigma if self.delta.get((q, a)) is not None]
            if not nexts:
                break
            a = nexts[int(rng.random() * len(nexts))]
            w, q = w + (a,), self.delta[(q, a)]
        return w

    def refused_task(self, rng, length):
        """A random word that the policy refuses: an allowed word, an action that is refused
        after it, and sometimes more.  None if the search finds no refusal."""
        for _ in range(20):
            w = self.task(rng, int(rng.random() * length))
            bad = [a for a in self.sigma if self.delta.get((self.run(w), a)) is None]
            if bad:
                w += (bad[int(rng.random() * len(bad))],)
                for _ in range(int(rng.random() * 3)):
                    w += (self.sigma[int(rng.random() * len(self.sigma))],)
                return w[:length]
        return None

    def stream(self, rng, count, length, share=0.0):
        """Tasks in the order in which they arrive; the given share of them is refused."""
        tasks = []
        for _ in range(count):
            t = self.refused_task(rng, length) if rng.random() < share else None
            tasks.append(t if t is not None else self.task(rng, 1 + int(rng.random() * length)))
        return tasks


class User:
    """The user knows the policy and answers three kinds of questions.  All are counted, and
    every answer is kept in order."""

    def __init__(self, policy):
        self.policy, self.log = policy, []
        self.asked = self.proposed = self.rejected = self.closings = self.reopened = 0

    def ask(self, w):
        """May the agent perform this sequence?"""
        self.asked += 1
        self.log.append(('ask', w, self.policy.allows(w)))
        return self.log[-1][2]

    def propose(self, plan):
        """May I work by this plan?  The user approves it, or names a sequence that the plan
        allows and the user does not."""
        self.proposed += 1
        bad = plan.beyond(self.policy)
        self.rejected += bad is not None
        self.log.append(('propose', plan, bad))
        return bad

    def close(self, plan):
        """Is this plan all that I may do?  The user confirms, or names a sequence that the
        user allows and the plan does not."""
        self.closings += 1
        more = self.policy.beyond(plan)
        self.reopened += more is not None
        self.log.append(('close', plan, more))
        return more

    def matters(self, a):
        """Does this action ever matter?  No, if the policy allows it after every allowed
        history and it changes nothing: the same histories are allowed with it and without."""
        self.asked += 1
        self.log.append(('matters', a, any(self.policy.delta.get((q, a)) != q for q in self.policy.states())))
        return self.log[-1][2]

    def consulted(self):
        return self.asked + self.proposed + self.closings


# ---------------------------------------------------------------------------------------------
# 2. The learner.  S holds access words and E experiments; T holds every answer that is known,
#    and `how` says where it came from: asked, or by closure under beginnings, or from the plan
#    that the user approved last.  Only the first kind costs the user anything.
# ---------------------------------------------------------------------------------------------

class Learner:
    def __init__(self, sigma, ask, search=True):
        self.sigma, self._ask, self.search = tuple(sigma), ask, search
        self.S, self.E, self.T, self.how = [()], [()], {}, {}
        self.yes, self.no = {()}, set()     # words known to be allowed; words known to be refused
        self.plan = None                     # the plan that the user approved last
        self.examples = []                   # counterexamples: (word, whether the user allows it)
        self.refined = 0                     # how often a counterexample has changed the table
        self._built = None
        self.close()

    def told(self, w, allowed):
        """What the user has said about a word.  An allowed word has allowed beginnings, and
        whatever continues a refused word is refused."""
        if allowed:
            self.yes.update(w[:i] for i in range(len(w) + 1))
        else:
            self.no.add(w)

    def member(self, w):
        if w in self.T:
            return self.T[w]
        if any(w[:i] in self.no for i in range(len(w) + 1)):
            ans, how = False, 'closure'
        elif w in self.yes and MUTANT != 'forgetful':
            ans, how = True, 'closure'
        elif self.plan is not None and self.plan.allows(w) and MUTANT != 'forgetful':
            ans, how = True, 'plan'
        else:
            ans, how = self._ask(w), 'asked'
            self.told(w, ans)
        if MUTANT == 'optimist' and not ans and len(w) > 2:
            ans = True
        self.T[w], self.how[w] = ans, how
        return ans

    def row(self, s):
        return tuple(self.member(s + e) for e in self.E)

    def close(self):
        """Adds access words until every row of a successor is the row of an access word."""
        while True:
            rows = {self.row(s) for s in self.S}
            for s in list(self.S):
                for a in self.sigma:
                    if self.row(s + (a,)) not in rows:
                        self.S.append(s + (a,))
                        break
                else:
                    continue
                break
            else:
                return

    def build(self):
        """The plan that the table describes, with one state for every row of an allowed
        access word, and the access word of every row."""
        self.close()
        name = {}
        for s in self.S:
            name.setdefault(self.row(s), s)
        delta = {}
        for r, s in name.items():
            if not self.member(s):
                continue
            for a in self.sigma:
                t = self.row(s + (a,))
                if self.member(name[t]):
                    delta[(r, a)] = t
        return Policy(self.sigma, self.row(()), delta), name

    def hypothesis(self):
        """The plan of the table, after the table has been corrected until the plan agrees with
        every counterexample that the learner has received."""
        stamp = (self.refined, len(self.examples))
        if self._built is not None and self._built[0] == stamp:
            return self._built[1]
        while True:
            plan, name = self.build()
            wrong = next((w for w, allowed in self.examples if plan.allows(w) != allowed), None)
            if wrong is None or MUTANT == 'deaf':
                self._built = ((self.refined, len(self.examples)), plan)
                return plan
            self.refine(wrong, plan, name)

    def refine(self, w, plan, name):
        """Corrects the table with a word on which its plan is wrong.  With search: follow the
        plan through the first i letters, go to the access word of the state reached, and ask
        about the rest.  For i = 0 the answer is the user's and for i = |w| it is the plan's, so
        it changes somewhere, and where it changes the rest of the word is a new experiment.
        Without search: every ending of the word becomes an experiment."""
        before = len(self.S)
        if self.search:
            def answer(i):
                q = plan.run(w[:i])
                return q is not None and self.member(name[q] + w[i:])
            lo, hi = 0, len(w)
            first = answer(0)
            assert answer(hi) != first, 'not a counterexample'
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if answer(mid) == first:
                    lo = mid
                else:
                    hi = mid
            new = [w[hi:]]
        else:
            new = [w[i:] for i in range(len(w) + 1)]
        self.E.extend(e for e in new if e not in self.E)
        self.close()
        assert len(self.S) > before, 'a counterexample that teaches nothing'
        self.refined += 1

    def counterexample(self, w, allowed):
        self.told(w, allowed)
        self.examples.append((w, allowed))


# ---------------------------------------------------------------------------------------------
# 3. Agents.  Each receives the tasks in order and performs or declines each.  It must perform
#    every task that the policy allows and no other.
# ---------------------------------------------------------------------------------------------

def escapes(plan, policy):
    """A word that the plan allows and the policy refuses, or None.  The tests use this
    search, which is written apart from the one that the user of the protocol uses."""
    seen, todo = {(plan.start, policy.start)}, [((), plan.start, policy.start)]
    while todo:
        w, p, q = todo.pop()
        for a in plan.sigma:
            p2 = plan.delta.get((p, a))
            if p2 is None:
                continue
            q2 = policy.delta.get((q, a))
            if q2 is None:
                return w + (a,)
            if (p2, q2) not in seen:
                seen.add((p2, q2))
                todo.append((w + (a,), p2, q2))
    return None


def learning_agent(policy, tasks, search=True, closing=False, sift=False, limit=200):
    """Section 4.  The agent keeps the plan that the user approved last.  A task within the
    plan needs nobody.  For a task outside it the agent asks about the task, tells the learner
    if the task is allowed, and proposes plans until the user approves one.  With `closing` it
    then asks whether the plan is all, and after a yes it declines without asking.  With `sift`
    it first asks of every action whether it ever matters, and learns over the others."""
    user = User(policy)
    idle = tuple(a for a in policy.sigma if sift and not user.matters(a))
    learner = Learner([a for a in policy.sigma if a not in idle], user.ask, search)

    def strip(w):
        return tuple(a for a in w if a not in idle)

    def lift(h):
        """The plan over all actions: those that never matter are allowed in every state."""
        return Policy(policy.sigma, h.start, {**h.delta, **{(q, a): q for q in h.states() for a in idle}})
    plan, version, final = None, None, False
    out = dict(examples=0, outside=0, paid=[], performed=[], first=None)
    for t in tasks:
        if plan is not None and plan.allows(t):
            out['performed'].append(True)
            continue
        if final:
            out['performed'].append(False)
            continue
        counted = False
        for _ in range(limit):
            h = lift(learner.hypothesis())
            if not h.allows(t):
                before = user.asked
                if MUTANT != 'timid' and learner.member(strip(t)):
                    out['outside'] += not counted
                    counted = True
                    learner.counterexample(strip(t), True)
                    out['examples'] += 1
                    continue
                if user.asked > before:
                    out['paid'].append((len(user.log) - 1, t))
            if MUTANT == 'hasty' and h.allows(t):
                plan, version = h, learner.refined
                break
            if plan is not None and version == learner.refined:
                break                                   # the approved plan is still the table's
            bad = user.propose(h)
            if bad is not None:
                learner.counterexample(strip(bad), False)
                out['examples'] += 1
                continue
            plan, version = h, learner.refined
            learner.plan = h
            if closing:
                more = user.close(h)
                if more is not None:
                    learner.counterexample(strip(more), True)
                    out['examples'] += 1
                    continue
                final = True
            break
        else:
            raise AssertionError('the learner does not settle')
        out['performed'].append(plan is not None and plan.allows(t))
        if out['first'] is None:
            out['first'] = user.consulted()
    out.update(asked=user.asked, proposed=user.proposed, rejected=user.rejected, closings=user.closings,
               reopened=user.reopened, total=user.consulted(), plan=plan, final=final, user=user,
               learner=learner, longest=max([len(w) for w, _ in learner.examples] or [1]))
    return out


def ask_always(policy, tasks):
    """Asks before every action, and stops a task at the first refusal."""
    asked = 0
    for t in tasks:
        for i in range(1, len(t) + 1):
            asked += 1
            if not policy.allows(t[:i]):
                break
    return asked


def remember_sequences(policy, tasks):
    """Asks before an action unless the same history with the same action was answered before."""
    seen = set()
    for t in tasks:
        for i in range(1, len(t) + 1):
            seen.add(t[:i])
            if not policy.allows(t[:i]):
                break
    return len(seen)


def lists(policy, tasks):
    """Section 5: the user may answer `always` or `never` for an action, and is careful: the
    first only for an action that the policy allows after every allowed history, the second
    only for one that it refuses after every allowed history.  Returns the questions and the
    actions for which the answer `always` is right."""
    states = policy.states()
    always = {a for a in policy.sigma if all(policy.delta.get((q, a)) is not None for q in states)}
    never = {a for a in policy.sigma if all(policy.delta.get((q, a)) is None for q in states)}
    asked, allow, deny = 0, set(), set()
    for t in tasks:
        q = policy.start
        for a in t:
            if a in deny:
                break
            if a not in allow:
                asked += 1
                if a in always:
                    allow.add(a)
                elif a in never:
                    deny.add(a)
            q = policy.delta.get((q, a))
            if q is None:
                break
    return asked, always


# ---------------------------------------------------------------------------------------------
# 4. Policies.
# ---------------------------------------------------------------------------------------------

ACTIONS = ('edit', 'test', 'commit', 'push')


def anything():
    return Policy(ACTIONS, 0, {(0, a): 0 for a in ACTIONS})


def no_push():
    """An allow-list: everything but push."""
    return Policy(ACTIONS, 0, {(0, a): 0 for a in ACTIONS if a != 'push'})


def test_first(extra=()):
    """A commit needs a test since the last edit, and a push needs a commit since the last
    edit.  Further actions are allowed everywhere and change nothing."""
    d = {}
    for q, a, t in [('dirty', 'edit', 'dirty'), ('dirty', 'test', 'tested'), ('tested', 'edit', 'dirty'),
                    ('tested', 'test', 'tested'), ('tested', 'commit', 'clean'), ('clean', 'edit', 'dirty'),
                    ('clean', 'test', 'clean'), ('clean', 'commit', 'clean'), ('clean', 'push', 'clean')]:
        d[(q, a)] = t
    for q in ('dirty', 'tested', 'clean'):
        for a in extra:
            d[(q, a)] = q
    return Policy(ACTIONS + tuple(extra), 'dirty', d)


def budget(k):
    """At most k pushes; everything else is free."""
    d = {}
    for i in range(k + 1):
        for a in ACTIONS:
            if a != 'push':
                d[(i, a)] = i
            elif i < k:
                d[(i, a)] = i + 1
    return Policy(ACTIONS, 0, d)


def release():
    """Edits and tests, then one commit, then one push, and nothing after it."""
    d = {('work', 'edit'): 'work', ('work', 'test'): 'work', ('work', 'commit'): 'committed',
         ('committed', 'push'): 'done'}
    return Policy(ACTIONS, 'work', d)


def without(word, sigma=('a', 'b')):
    """Everything in which the given word does not occur as a block."""
    n = len(word)

    def step(q, a):
        s = word[:q] + (a,)
        while s and s != word[:len(s)]:
            s = s[1:]
        return len(s)

    d = {}
    for q in range(n):
        for a in sigma:
            t = step(q, a)
            if t < n:
                d[(q, a)] = t
    return Policy(sigma, 0, d)


def random_policy(rng, n, sigma=ACTIONS, p=0.25):
    """A random policy with n states, every one of which is reached."""
    d = {}
    for q in range(1, n):
        d[(int(rng.random() * q), sigma[int(rng.random() * len(sigma))])] = q
    for q in range(n):
        for a in sigma:
            if (q, a) not in d and rng.random() > p:
                d[(q, a)] = int(rng.random() * n)
    return Policy(sigma, 0, d)


def either(policy, word):
    """The policy that allows what the given one allows and, besides, the word and its
    beginnings.  Proposition 4.7 uses it: it is the policy that the user might have had."""
    start = (policy.start, 0)
    delta, seen, todo = {}, {start}, [start]
    while todo:
        q, i = todo.pop()
        for a in policy.sigma:
            q2 = policy.delta.get((q, a)) if q is not None else None
            i2 = i + 1 if i is not None and i < len(word) and word[i] == a else None
            if q2 is None and i2 is None:
                continue
            delta[((q, i), a)] = (q2, i2)
            if (q2, i2) not in seen:
                seen.add((q2, i2))
                todo.append((q2, i2))
    return Policy(policy.sigma, start, delta)


SHAPES = [('anything', anything), ('everything but push', no_push), ('test before commit', test_first),
          ('three pushes', lambda: budget(3)), ('one release', release)]


# ---------------------------------------------------------------------------------------------
# 5. The tests.
# ---------------------------------------------------------------------------------------------

def log2ceil(m):
    return max(m - 1, 0).bit_length()


def same_answers(log, other):
    """Whether every answer in the log would also be a right answer of a user with the other
    policy."""
    for kind, what, answer in log:
        if kind == 'ask':
            ok = other.allows(what) == answer
        elif answer is None:
            ok = escapes(what, other) is None if kind == 'propose' else escapes(other, what) is None
        elif kind == 'propose':
            ok = what.allows(answer) and not other.allows(answer)
        else:
            ok = other.allows(answer) and not what.allows(answer)
        if not ok:
            return False
    return True


KINDS = [('search', True, False), ('plain', False, False), ('search-closing', True, True),
         ('plain-closing', False, True)]
FIELDS = ('policies', 'states', 'refusals') + tuple(f'{k}-{f}' for k, _, _ in KINDS
                                                    for f in ('asked', 'examples', 'most', 'exact', 'paid'))


def trial(rng, counts):
    """Theorems 4.3 to 4.8 and Proposition 4.7 on one random policy and one random sequence of
    tasks, about a fifth of which the policy refuses."""
    n = 2 + int(rng.random() * 9)
    policy = random_policy(rng, n)
    size = policy.size()
    tasks = policy.stream(rng, 150, 12, 0.2)
    allowed = [policy.allows(t) for t in tasks]
    sigma = len(policy.sigma)
    for kind, search, closing in KINDS:
        out = learning_agent(policy, tasks, search, closing)
        plan, learner = out['plan'], out['learner']
        assert out['performed'] == allowed, 'a refused task is performed, or an allowed one declined'
        assert escapes(plan, policy) is None, 'an approved plan allows what the policy refuses'
        assert out['examples'] <= learner.refined <= max(size - 1, 0), ('too many counterexamples', size)
        assert search or out['examples'] == learner.refined, 'the plain learner is wrong twice about one history'
        assert out['rejected'] + out['reopened'] + out['outside'] <= out['examples'] + 1, 'a correction without a counterexample'
        m, paid = out['longest'], len(out['paid'])
        tasks_asked = 1 if closing else size + paid if search else paid
        if search:
            bound = size * size * (1 + sigma) + (size - 1) * log2ceil(m) + tasks_asked
        else:
            bound = size * (1 + sigma) * (1 + m * (size - 1)) + tasks_asked
        assert out['asked'] <= bound, ('too many questions', out['asked'], bound)
        if closing:
            assert out['final'] and escapes(policy, plan) is None, 'a closed plan is not the policy'
            assert out['first'] == out['total'], 'a question after the plan was closed'
        else:
            # Proposition 4.7: when the agent paid for a refused task, the user might as well
            # have had the policy that allows the task; every earlier answer fits that one too.
            for index, t in out['paid']:
                assert same_answers(out['user'].log[:index], either(policy, t)), 'a question that was not needed'
        counts[f'{kind}-asked'] += out['asked']
        counts[f'{kind}-examples'] += out['examples']
        counts[f'{kind}-most'] = max(counts[f'{kind}-most'], out['asked'])
        counts[f'{kind}-exact'] += escapes(policy, plan) is None
        counts[f'{kind}-paid'] += paid
    counts['policies'] += 1
    counts['states'] += size
    counts['refusals'] += allowed.count(False)


MUTANTS = ('careless-user', 'optimist', 'deaf', 'forgetful', 'hasty', 'timid')
BASELINE = {}


def catches(name):
    """How the tests notice the mistake: the check that fails, or, for the learner that
    forgets what follows from closure under beginnings, that the questions go up.  None if
    they do not notice."""
    global MUTANT
    MUTANT = name
    rng, counts = random.Random(2026), dict.fromkeys(FIELDS, 0)
    try:
        for _ in range(60):
            trial(rng, counts)
        return 'more questions' if counts['search-asked'] > BASELINE['search-asked'] else None
    except AssertionError as failed:
        return str(failed.args[0] if isinstance(failed.args[0], str) else failed.args[0][0])
    finally:
        MUTANT = None


def words(w, short=False):
    if not w:
        return '$\\varepsilon$'
    return ' '.join(a[0] for a in w) if short else '$' + '\\ '.join(f'\\nm{{{a}}}' for a in w) + '$'


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten']

    # Section 4 on random policies
    base, base_rng = dict.fromkeys(FIELDS, 0), random.Random(2026)
    for _ in range(60):
        trial(base_rng, base)
    BASELINE.update(base)
    counts = dict.fromkeys(FIELDS, 0)
    for _ in range(1000):
        trial(rng, counts)
    claim('bounds', counts['policies'] == 1000)
    claim('exact', counts['search-exact'] == counts['plain-exact'] == 1000)
    claim('closing', counts['search-closing-exact'] == counts['plain-closing-exact'] == 1000
          and counts['search-closing-paid'] <= 1000)
    claim('refusals-cost', counts['search-paid'] > 10000)
    lines.append(f"{counts['policies']} random policies with {counts['states']} states in all, 150 tasks each, "
                 f"{counts['refusals']} of the tasks refused: every agent performs the allowed tasks and no other, "
                 f"every approved plan is within the policy, and the counterexamples and questions are within the bounds")
    for kind, _, _ in KINDS:
        lines.append(f"  {kind}: {counts[kind + '-examples']} counterexamples, {counts[kind + '-asked']} questions "
                     f"(at most {counts[kind + '-most']} for one policy), {counts[kind + '-paid']} of them for refused "
                     f"tasks; {counts[kind + '-exact']} final plans are the policy itself")
    nums.update(Policies=f"{counts['policies']:,}", StatesAll=f"{counts['states']:,}", TasksEach='150',
                Refusals=f"{counts['refusals']:,}", Examples=f"{counts['search-examples']:,}",
                ExamplesPlain=f"{counts['plain-examples']:,}",
                ExamplesClosing=f"{counts['search-closing-examples']:,}",
                AskedMean=str(round((counts['search-asked'] - counts['search-paid']) / counts['policies'])),
                AskedMeanPlain=str(round((counts['plain-asked'] - counts['plain-paid']) / counts['policies'])),
                AskedMeanClosing=str(round(counts['search-closing-asked'] / counts['policies'])),
                Paid=f"{counts['search-paid']:,}")

    # Section 2: the dialogue for the first task under `test before commit`
    policy, first = test_first(), ('edit', 'test', 'commit', 'push')
    out = learning_agent(policy, [first])
    log, learner, plan = out['user'].log, out['learner'], out['plan']
    cells = []
    for kind, what, answer in log:
        if kind == 'ask':
            cells.append((f'may I do {words(what)}?', 'yes' if answer else 'no'))
            lines.append(f"dialogue: {' '.join(what)}? {'yes' if answer else 'no'}")
        else:
            cells.append(('may I work by the plan of Figure~\\ref{fig:plan}?', 'yes' if answer is None else 'no'))
            lines.append(f"dialogue: a plan with {len(what.states())} states? {'yes' if answer is None else 'no'}")
    half = (len(cells) + 1) // 2
    cells.append(('', ''))
    tables['dialogue'] = [f'{cells[i][0]} & {cells[i][1]} & {cells[i + half][0]} & {cells[i + half][1]} \\\\'
                          for i in range(half)]
    plain = learning_agent(policy, [first], search=False)
    claim('example', out['asked'] + 1 == len(log) and log[-1][0] == 'propose' and log[-1][2] is None
          and escapes(policy, plan) is None and escapes(plan, policy) is None and len(plan.states()) == 3
          and [a for _, _, a in log[:4]] == [True, True, False, False]
          and [w for _, w, _ in log[4:7]] == [first, first[1:], ('edit',) + first[2:]]
          and learner.E == [(), ('commit', 'push'), ('push',)] and out['rejected'] == 0)
    lines.append(f"dialogue: {out['asked']} questions and one proposal, which is the policy and is approved; "
                 f"the plain learner asks {plain['asked']}")
    nums.update(DialogueAsked=str(out['asked']), DialoguePlain=str(plain['asked']))

    # Figure 2: the table of the learner at the end of the dialogue
    rows, heads = [], learner.S + [s + (a,) for s in learner.S for a in learner.sigma if s + (a,) not in learner.S]
    for s in heads:
        row = []
        for e in learner.E:
            answer = 'yes' if learner.T[s + e] else 'no'
            row.append(answer if learner.how[s + e] == 'asked' else f'\\textcolor{{gray}}{{({answer})}}')
        rows.append(f"{words(s, True)} & {' & '.join(row)} \\\\" + ('\n\\midrule' if s == learner.S[-1] else ''))
    tables['cells'] = rows
    held = {s + e for s in heads for e in learner.E}
    put = {w for w in held if learner.how[w] == 'asked'}
    claim('cells', len(put) + 1 == out['asked'] and learner.how[first] == 'asked' and first not in held
          and learner.S == [(), ('commit',), ('test',), ('test', 'commit')])
    lines.append(f'the table of the example: {len(learner.S)} access words, {len(rows)} rows, '
                 f'{len(rows) * len(learner.E)} cells with {len(held)} different words, {len(put)} of them asked about')
    nums.update(CellRows=str(len(rows)), CellWords=str(len(held)), CellsAsked=str(len(put)),
                CellsFree=str(len(held) - len(put)))

    # Table 4: policies of five shapes, the same tasks for every agent
    rows, shapes = [], {}
    for name, make in SHAPES:
        policy = make()
        tasks = policy.stream(rng, 300, 12)
        out = learning_agent(policy, tasks)
        assert escapes(out['plan'], policy) is None and all(out['performed'])
        listed, always = lists(policy, tasks)
        named = [answer for kind, _, answer in out['user'].log if kind == 'propose' and answer is not None]
        row = (policy.size(), ask_always(policy, tasks), remember_sequences(policy, tasks), listed, out['asked'],
               out['proposed'], out['rejected'], out['outside'], named)
        shapes[name] = row
        lines.append(f"{name}: {row[0]} states; questions: always {row[1]}, remembered {row[2]}, lists {row[3]} "
                     f"(always for {len(always)} actions); learner: {row[4]} questions, {row[5]} proposals, {row[6]} "
                     f"rejected, {row[7]} tasks outside the plan")
        rows.append(f"{name} & {row[0]} & {row[1]:,} & {row[2]:,} & {row[3]:,} & {row[4]} & {row[5]} & {row[6]} & {row[7]} \\\\")
    tables['shapes'] = rows
    memory = ('test before commit', 'three pushes', 'one release')
    claim('shapes', shapes['anything'][3] == shapes['everything but push'][3] + 1 == len(ACTIONS)
          and all(shapes[s][4] + shapes[s][5] <= len(ACTIONS) + 1 for s in ('anything', 'everything but push'))
          and all(9 * (shapes[s][4] + shapes[s][5]) < shapes[s][3] for s in memory)
          and all(r[6] + r[7] <= r[0] for r in shapes.values())
          and [s for s, r in shapes.items() if r[6]] == ['three pushes', 'one release']
          and shapes['three pushes'][8] == [('push',) * 4])
    nums.update(ShapeTasks='300')

    # Table 5: the questions of the lists grow with the work, those of the learner do not
    rows, policy = [], test_first()
    stream = policy.stream(rng, 10000, 12)
    last, even = None, None
    for n in (100, 1000, 10000):
        out, plain = learning_agent(policy, stream[:n]), learning_agent(policy, stream[:n], search=False)
        listed, always = lists(policy, stream[:n])
        last = (ask_always(policy, stream[:n]), remember_sequences(policy, stream[:n]), listed,
                plain['total'], out['total'])
        rows.append(f"{n:,} & {last[0]:,} & {last[1]:,} & {last[2]:,} & {last[3]} & {last[4]} \\\\")
        lines.append(f'test before commit, {n} tasks: always {last[0]}, remembered {last[1]}, lists {last[2]}, '
                     f'plain learner {last[3]}, learner {last[4]}')
    for n in range(1, 10001):
        if lists(policy, stream[:n])[0] > last[4]:
            even = n
            break
    tables['growth'] = rows
    claim('growth', last[4] < 50 and last[2] > 10000 and sorted(always) == ['edit', 'test'] and even < 100
          and learning_agent(policy, stream[:even])['total'] == last[4])
    lines.append(f'the lists have asked more than the learner ever asks after {even} tasks')
    nums.update(GrowthLearner=str(last[4]), GrowthPlain=str(last[3]), GrowthList=f'{last[2]:,}', Even=str(even))

    # Table 6: refused tasks, with and without the closing question
    rows, policy, kept = [], test_first(), {}
    for share in (0, 10, 25, 50):
        tasks = policy.stream(rng, 1000, 12, share / 100)
        refused = sum(not policy.allows(t) for t in tasks)
        lazy, closed = learning_agent(policy, tasks), learning_agent(policy, tasks, closing=True)
        assert lazy['performed'] == closed['performed'] == [policy.allows(t) for t in tasks]
        kept[share] = (refused, ask_always(policy, tasks), remember_sequences(policy, tasks), lists(policy, tasks)[0],
                       lazy['total'], len(lazy['paid']), closed['total'])
        r = kept[share]
        rows.append(f"{r[0]} & {r[1]:,} & {r[2]:,} & {r[3]:,} & {r[4]} & {r[6]} \\\\")
        lines.append(f'test before commit, 1000 tasks, {r[0]} refused: always {r[1]}, remembered {r[2]}, lists {r[3]}, '
                     f'learner {r[4]} ({r[5]} for refused tasks), learner with closing {r[6]}')
    tables['refused'] = rows
    chain = [('edit',) * k + ('commit',) for k in range(1, 101)]
    lazy, closed = learning_agent(policy, [first] + chain), learning_agent(policy, [first] + chain, closing=True)
    claim('refused', kept[0][0] == 0 and kept[50][4] > 5 * kept[0][4] and len(lazy['paid']) == len(chain)
          and len({r[6] for r in kept.values()}) <= 2 and max(r[6] for r in kept.values()) < 40
          and closed['total'] == closed['first'] and not any(closed['performed'][1:]))
    lines.append(f"the tasks edit^k commit for k = 1..{len(chain)} after the first task: {len(lazy['paid'])} questions "
                 f"without closing, {closed['total'] - closed['first']} with it")
    nums.update(RefusedTasks='1,000', Chain=str(len(chain)), ChainPaid=str(len(lazy['paid'])))

    # Table 7: long tasks, with and without the search
    rows, policy, kept = [], test_first(), []
    for longest in (12, 50, 200, 800):
        tasks = [policy.task(rng, longest) for _ in range(200)]
        out, plain = learning_agent(policy, tasks), learning_agent(policy, tasks, search=False)
        kept.append((plain['asked'], out['asked']))
        rows.append(f"{longest} & {plain['asked']:,} & {out['asked']} \\\\")
        lines.append(f"test before commit, 200 tasks of {longest} actions: plain learner {plain['asked']} questions, "
                     f"with search {out['asked']}")
    tables['lengths'] = rows
    claim('lengths', kept[-1][0] > 20 * kept[0][0] and kept[-1][1] < 2 * kept[0][1])
    nums.update(LengthPlain=f'{kept[-1][0]:,}', LengthSearch=str(kept[-1][1]))

    # Table 8: actions that never matter still cost questions, unless the user says so
    rows, kept = [], []
    core = test_first().stream(rng, 300, 12)
    for extra in (0, 4, 12, 28):
        names = tuple(f'x{i}' for i in range(extra))
        policy, tasks = test_first(names), []
        for t in core:                        # the same work, with other actions in between
            w = ()
            for a in t:
                w += (a,)
                for _ in range(int(rng.random() * 3) if names else 0):
                    w += (names[int(rng.random() * extra)],)
            tasks.append(w)
        out, sifted = learning_agent(policy, tasks), learning_agent(policy, tasks, sift=True)
        for o in (out, sifted):
            assert escapes(o['plan'], policy) is None and escapes(policy, o['plan']) is None and all(o['performed'])
        kept.append((len(policy.sigma), lists(policy, tasks)[0], out['total'], sifted['total']))
        rows.append(f"{kept[-1][0]} & {kept[-1][1]:,} & {kept[-1][2]} & {kept[-1][3]} \\\\")
        lines.append(f'test before commit with {extra} more actions that change nothing, 300 tasks: lists '
                     f'{kept[-1][1]}, learner {kept[-1][2]}, learner that first asks which actions matter {kept[-1][3]}')
    tables['alphabet'] = rows
    claim('alphabet', kept[-1][2] > 4 * kept[0][2] and all(r[1] == kept[0][1] + r[0] - len(ACTIONS) for r in kept)
          and all(r[3] == kept[0][3] + r[0] - len(ACTIONS) for r in kept) and kept[-1][3] < kept[-1][2] / 3)
    nums.update(AlphabetLearner=str(kept[-1][2]), AlphabetSifted=str(kept[-1][3]))

    # Proposition 5.3: a forbidden block
    rows, kept = [], []
    for k in range(2, 9):
        word = tuple('ab'[(i * i + i // 2) % 2] for i in range(k))
        policy = without(word)
        tasks = [policy.task(rng, 2 * k) for _ in range(50)]
        out = learning_agent(policy, tasks)
        assert escapes(out['plan'], policy) is None and escapes(policy, out['plan']) is None, k
        kept.append((policy.size(), out['asked'], out['proposed'], out['rejected']))
        rows.append(f"{k} & {kept[-1][0]} & {kept[-1][1]} & {kept[-1][2]} & {kept[-1][3]} & {2 ** k} \\\\")
        lines.append(f"a forbidden block of {k} letters: {kept[-1][0]} states, learned exactly with {kept[-1][1]} "
                     f"questions and {kept[-1][2]} proposals, {kept[-1][3]} rejected; {2 ** k} blocks of that length")
    tables['blocks'] = rows
    every, once = 0, 0
    for k in range(2, 9):
        for code in range(2 ** k):
            policy = without(tuple('ab'[code >> i & 1] for i in range(k)))
            for search in (True, False):
                out = learning_agent(policy, [policy.task(rng, 2 * k)], search)
                once += out['rejected'] == 1 and out['proposed'] == 2 and escapes(policy, out['plan']) is None
            every += 1
    claim('blocks', all(r[0] == k + 1 for k, r in zip(range(2, 9), kept)) and kept[-1][1] < 2 ** 8
          and once == 2 * every)
    lines.append(f'every one of the {every} blocks of two to eight letters, both learners: one rejected proposal, '
                 f'and the second proposal is the policy')
    nums.update(BlocksAll=str(every))

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values())
          and [name for name in MUTANTS if caught[name] == 'more questions'] == ['forgetful'])
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed:')
    lines.extend(f'  {name}: {caught[name]}' for name in MUTANTS)
    nums.update(Mutants=spelled[len(MUTANTS)], Seed='2026',
                Lines=f"{round(len(open(os.path.join(here, 'learn.py')).readlines()), -2):,}")

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
        f.write('% written by learn.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by learn.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
