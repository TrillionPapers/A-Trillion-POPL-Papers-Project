#!/usr/bin/env python3
"""Tests the claims of "A Budget Is a Distance" on an implementation of its decoder.

The file has five parts.

1. Schemas as automata over characters, and a small compiler from regular expressions.
2. Vocabularies: a token is a string, and a token moves the automaton by all its characters.
   The distance of a state in tokens and in characters, and the same by trying every sequence
   of tokens.  Only the trying is trusted.
3. Masks and what a decoder can do under them (Theorems 3.1 to 3.5), masks made from the
   distance in characters (Proposition 4.1), and budgets in another unit, alone or together
   with a budget in tokens (Theorems 6.1 and 6.2).
4. Pushdown schemas: the distance of a configuration from summaries and one pass over its
   stack (Theorem 5.1).
5. The tests.  `python3 budget.py out` writes out/check.txt, out/numbers.tex and the table.

A test is not a proof.  The proofs are in the paper.
"""
import math
import os
import random
import sys
from itertools import product

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked
FAR = math.inf


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. An automaton is its states, a start state, its accepting states, and a partial map from
#    (state, character) to a state.
# ---------------------------------------------------------------------------------------------

def compile_expression(text):
    """The automaton of a regular expression with ( ) | * + ? and classes like [ab].  A
    backslash takes the next character as it is."""
    edges, count, at = {}, [0], [0]                     # edges of the automaton with empty moves

    def state():
        count[0] += 1
        return count[0] - 1

    def edge(a, label, b):
        edges.setdefault((a, label), set()).add(b)

    def expression():
        first, last = term()
        while at[0] < len(text) and text[at[0]] == '|':
            at[0] += 1
            other_first, other_last = term()
            a, b = state(), state()
            for x in (first, other_first):
                edge(a, None, x)
            for x in (last, other_last):
                edge(x, None, b)
            first, last = a, b
        return first, last

    def term():
        first = last = state()
        while at[0] < len(text) and text[at[0]] not in '|)':
            a, b = factor()
            edge(last, None, a)
            last = b
        return first, last

    def factor():
        a, b = atom()
        while at[0] < len(text) and text[at[0]] in '*+?':
            sign = text[at[0]]
            at[0] += 1
            first, last = state(), state()
            edge(first, None, a)
            edge(b, None, last)
            if sign in '*?':
                edge(first, None, last)
            if sign in '*+':
                edge(b, None, a)
            a, b = first, last
        return a, b

    def atom():
        c = text[at[0]]
        at[0] += 1
        if c == '(':
            a, b = expression()
            at[0] += 1                                  # the closing bracket
            return a, b
        a, b = state(), state()
        if c == '[':
            while text[at[0]] != ']':
                edge(a, text[at[0]], b)
                at[0] += 1
            at[0] += 1
        else:
            if c == '\\':
                c = text[at[0]]
                at[0] += 1
            edge(a, c, b)
        return a, b

    first, last = expression()

    def closure(states):
        todo, seen = list(states), set(states)
        while todo:
            for x in edges.get((todo.pop(), None), ()):
                if x not in seen:
                    seen.add(x)
                    todo.append(x)
        return frozenset(seen)

    start = closure({first})
    names, delta, todo = {start: 0}, {}, [start]
    letters = sorted({label for _, label in edges if label is not None})
    while todo:
        here = todo.pop()
        for c in letters:
            there = closure({x for a in here for x in edges.get((a, c), ())})
            if there:
                if there not in names:
                    names[there] = len(names)
                    todo.append(there)
                delta[names[here], c] = names[there]
    return dict(states=list(range(len(names))), start=0, delta=delta,
                finals={name for subset, name in names.items() if last in subset})


def accepts(automaton, state, text):
    """Whether the text leads from the state to an accepting state.  This is the definition."""
    for c in text:
        state = automaton['delta'].get((state, c))
        if state is None:
            return False
    return state in automaton['finals']


# ---------------------------------------------------------------------------------------------
# 2. Tokens.
# ---------------------------------------------------------------------------------------------

def step(automaton, state, token):
    """The state after the token, or None."""
    for c in token[:1] if MUTANT == 'first-character' else token:
        state = automaton['delta'].get((state, c))
        if state is None:
            return None
    return state


def distance(automaton, tokens):
    """The fewest tokens from every state to an accepting state: a search backwards from the
    accepting states over the graph whose edges are the tokens.  A state from which no
    sequence of tokens is accepted has no entry."""
    back = {}
    for q in automaton['states']:
        for token in tokens:
            p = step(automaton, q, token)
            if p is not None:
                back.setdefault(p, set()).add(q)
    if MUTANT == 'forward':                             # the distance from the start instead
        found, front = {automaton['start']: 0}, [automaton['start']]
        while front:
            q = front.pop(0)
            for token in tokens:
                p = step(automaton, q, token)
                if p is not None and p not in found:
                    found[p] = found[q] + 1
                    front.append(p)
        return found
    found, front = {q: 0 for q in automaton['finals']}, list(automaton['finals'])
    while front:
        p = front.pop(0)
        for q in back.get(p, ()):
            if q not in found:
                found[q] = found[p] + 1
                front.append(q)
    return found


def priced_distance(automaton, tokens, price):
    """Theorem 6.1: the least total price of tokens from every state to an accepting state,
    where every token has a price above zero."""
    found = {q: 0 for q in automaton['finals']}
    changed = True
    while changed:                                      # few states: no queue is needed
        changed = False
        for q in automaton['states']:
            for token in tokens:
                p = step(automaton, q, token)
                if p in found and found[p] + price[token] < found.get(q, FAR):
                    found[q] = found[p] + price[token]
                    changed = True
    return found


def within(automaton, tokens, price, most):
    """Theorem 6.2: least[n][q] is the least total price of at most n tokens from q to an
    accepting state, for n up to `most`."""
    least = [{q: 0 for q in automaton['finals']}]
    for _ in range(most):
        before, now = least[-1], dict(least[-1])
        for q in automaton['states']:
            for token in tokens:
                p = step(automaton, q, token)
                if p in before and before[p] + price[token] < now.get(q, FAR):
                    now[q] = before[p] + price[token]
        least.append(now)
    return least


def characters(automaton):
    return sorted({c for _, c in automaton['delta']})


def fewest_by_force(automaton, tokens, state, most):
    """The fewest tokens, at most `most`, that are accepted from the state, by trying every
    sequence; None if there is none."""
    for size in range(most + 1):
        if any(accepts(automaton, state, ''.join(chosen)) for chosen in product(tokens, repeat=size)):
            return size
    return None


# ---------------------------------------------------------------------------------------------
# 3. A decoder is in a state with some tokens left.  A mask says which tokens it may emit next.
#    It may stop only in an accepting state.  It fails if it is not in an accepting state and
#    has no tokens left or may emit none.
# ---------------------------------------------------------------------------------------------

def budget_mask(automaton, tokens, far, state, left):
    """Theorem 3.1: the tokens after which what is left of the budget is still enough."""
    spare = left if MUTANT == 'off-by-one' else left - 1
    return [token for token in tokens if far.get(step(automaton, state, token), FAR) <= spare]


def live_mask(automaton, tokens, alive, state, left):
    """The usual mask: the tokens after which the output can still be completed, by `alive`."""
    return [token for token in tokens if step(automaton, state, token) in alive]


def may_stop(automaton, far, state):
    return state in far if MUTANT == 'stop-alive' else state in automaton['finals']


def reachable(automaton, mask, budget):
    """Every (state, tokens left) that some run of the decoder reaches."""
    seen, todo = {(automaton['start'], budget)}, [(automaton['start'], budget)]
    while todo:
        q, left = todo.pop()
        if left:
            for token in mask(q, left):
                there = (step(automaton, q, token), left - 1)
                if there not in seen:
                    seen.add(there)
                    todo.append(there)
    return seen


def safe(automaton, mask, budget):
    """Whether no run fails."""
    return all(q in automaton['finals'] or (left and mask(q, left)) for q, left in reachable(automaton, mask, budget))


def outputs(automaton, far, mask, budget):
    """Every sequence of tokens after which the decoder may stop."""
    found, todo = set(), [((), automaton['start'], budget)]
    while todo:
        said, q, left = todo.pop()
        if may_stop(automaton, far, q):
            found.add(said)
        if left:
            for token in mask(q, left):
                todo.append((said + (token,), step(automaton, q, token), left - 1))
    return found


# ---------------------------------------------------------------------------------------------
# 4. A pushdown schema reads one character at a time.  A move depends on the state, the
#    character and the top of the stack ('' if the stack is empty), and it keeps the stack,
#    pushes a symbol or pops one.  It accepts in an accepting state with an empty stack.
#    A configuration is (state, stack), the top of the stack first.
# ---------------------------------------------------------------------------------------------

def push_step(schema, configuration, token):
    state, stack = configuration
    for c in token:
        move = schema['moves'].get((state, c, stack[0] if stack else ''))
        if move is None:
            return None
        state, (what, *symbol) = move
        stack = (symbol[0],) + stack if what == 'push' else stack[1:] if what == 'pop' else stack
    return state, stack


def push_accepts(schema, configuration):
    return configuration[0] in schema['finals'] and not configuration[1]


def summaries(schema, tokens):
    """Theorem 5.1.  A point is a state and a piece of a token that has been begun ('' between
    two tokens).  level[f][x][y] is the fewest tokens that are completed on a way from point x
    to point y on which the top of the stack is f at both ends and the stack never gets lower.
    Returns the function that gives the distance of a configuration."""
    begun = sorted({token[:i] for token in tokens for i in range(len(token))})
    points = [(q, piece) for q in schema['states'] for piece in begun]
    tops = [''] + schema['symbols']

    def read(piece, c):                                 # where reading c leaves a begun token, and the price
        longer = piece + c
        return ([(longer, 0)] if longer in begun else []) + ([('', 1)] if longer in tokens else [])

    def closed(direct):
        best = {x: dict(direct[x]) for x in points}
        for x in points:
            best[x][x] = 0
        for via in points:
            for x in points:
                first = best[x].get(via, FAR)
                if first < FAR:
                    for y, second in best[via].items():
                        if first + second < best[x].get(y, FAR):
                            best[x][y] = first + second
        return best

    level = {f: {x: {x: 0} for x in points} for f in tops}
    while True:
        fresh = {}
        for f in tops:
            direct = {x: {} for x in points}
            for (q, c, top), (q1, (what, *symbol)) in schema['moves'].items():
                if top != f or what == 'pop':
                    continue
                for piece in begun:
                    for piece1, price1 in read(piece, c):
                        if what == 'keep':
                            ways = [((q1, piece1), price1)]
                        else:                           # push g, stay on that level, pop g
                            ways = []
                            for (q2, piece2), inside in level[symbol[0]][q1, piece1].items():
                                for (q3, c2, top2), (q4, (what2, *_)) in schema['moves'].items():
                                    if q3 == q2 and top2 == symbol[0] and what2 == 'pop':
                                        ways += [((q4, piece3), price1 + inside + price3) for piece3, price3 in read(piece2, c2)]
                        for y, price in ways:
                            if price < direct[q, piece].get(y, FAR):
                                direct[q, piece][y] = price
            fresh[f] = closed(direct)
        if fresh == level:
            break
        level = fresh

    down = {}                                           # down[f][x][y]: from x to y, where the last move pops f
    for f in schema['symbols']:
        down[f] = {x: {} for x in points}
        for x in points:
            for (q2, piece2), price in level[f][x].items():
                for (q3, c, top), (q4, (what, *_)) in schema['moves'].items():
                    if q3 == q2 and top == f and what == 'pop':
                        for piece3, price3 in read(piece2, c):
                            if MUTANT == 'whole-tokens' and piece3:
                                continue                # no token may reach across a pop
                            if price + price3 < down[f][x].get((q4, piece3), FAR):
                                down[f][x][q4, piece3] = price + price3
    finish = {x: min([level[''][x].get((q, ''), FAR) for q in schema['finals']], default=FAR) for x in points}

    def far(configuration):
        state, stack = configuration
        rest = finish
        for f in (stack if MUTANT == 'top-first' else reversed(stack)):
            rest = {x: min([price + rest[y] for y, price in down[f][x].items()], default=FAR) for x in points}
        return rest[state, '']

    return far


def push_fewest(schema, tokens, configuration, most):
    """The fewest tokens, at most `most`, from the configuration to acceptance, by a search over
    configurations; None if there is none."""
    seen, front = {configuration}, [configuration]
    for size in range(most + 1):
        if any(push_accepts(schema, c) for c in front):
            return size
        following = []
        for c in front:
            for token in tokens:
                there = push_step(schema, c, token)
                if there is not None and there not in seen:
                    seen.add(there)
                    following.append(there)
        front = following
    return None


# ---------------------------------------------------------------------------------------------
# 5. The tests.
# ---------------------------------------------------------------------------------------------

MUTANTS = ('off-by-one', 'forward', 'first-character', 'stop-alive', 'cheapest-only', 'whole-tokens', 'top-first')


def random_automaton(rng):
    letters = 'ab' if rng.random() < 0.5 else 'abc'
    n = rng.randrange(2, 7)
    delta = {(q, c): rng.randrange(n) for q in range(n) for c in letters if rng.random() < 0.6}
    finals = {q for q in range(n) if rng.random() < 0.3} or {rng.randrange(n)}
    tokens = set()
    if rng.random() < 0.5:
        tokens |= set(letters)                          # every character is a token, as in real vocabularies
    while len(tokens) < rng.randrange(2, 6):
        tokens.add(''.join(rng.choice(letters) for _ in range(rng.randrange(1, 4))))
    return dict(states=list(range(n)), start=0, delta=delta, finals=finals), sorted(tokens), letters


def check_regular(rng, counts):
    """Theorems 3.1 to 3.5 and Proposition 4.1 on one random automaton and vocabulary."""
    automaton, tokens, letters = random_automaton(rng)
    far = distance(automaton, tokens)
    by_letter = distance(automaton, list(letters))
    longest = max(len(token) for token in tokens)
    most = 4
    for q in automaton['states']:
        forced = fewest_by_force(automaton, tokens, q, most)
        assert forced == (far[q] if far.get(q, FAR) <= most else None), 'the distance in tokens differs from trying every sequence'
        if q in by_letter and q not in far:
            counts['dead'] += 1                         # completable by characters, not by tokens
    if set(letters) <= set(tokens):
        assert set(far) == set(by_letter), 'with every character a token, a state is alive for one and dead for the other'
        assert all(by_letter[q] <= longest * far[q] and far[q] <= by_letter[q] for q in far), 'the bounds by characters fail'
    budget = rng.randrange(0, 5)
    mask = lambda q, left: budget_mask(automaton, tokens, far, q, left)
    start = automaton['start']
    possible = far.get(start, FAR) <= budget
    # Theorem 3.4: the request can be refused before anything is generated
    assert possible == (fewest_by_force(automaton, tokens, start, budget) is not None), 'the check before the first token is wrong'
    wanted = {chosen for size in range(budget + 1) for chosen in product(tokens, repeat=size)
              if accepts(automaton, start, ''.join(chosen))}
    if possible:
        assert safe(automaton, mask, budget), 'a run under the budget mask fails'          # Theorem 3.1
        counts['safe'] += 1
    assert outputs(automaton, far, mask, budget) == wanted, 'the outputs under the budget mask are not the accepted sequences'  # 3.2
    counts['outputs'] += len(wanted)
    # Theorem 3.3: a token that the mask forbids has no completion in what is left
    for q in automaton['states']:
        for left in range(1, budget + 1):
            allowed = mask(q, left)
            for token in tokens:
                there = step(automaton, q, token)
                if there is not None and token not in allowed:
                    assert fewest_by_force(automaton, tokens, there, left - 1) is None, 'a forbidden token could have been completed'
                    counts['forbidden'] += 1
    # Theorem 3.5: with more tokens left than the largest distance, the mask is the usual one
    widest = max(far.values(), default=0)
    for q in automaton['states']:
        assert mask(q, widest + 1) == live_mask(automaton, tokens, set(far), q, 0), 'far from the end the mask differs from the usual one'
    # the usual mask, with liveness by characters: runs can fail
    usual = lambda q, left: live_mask(automaton, tokens, set(by_letter), q, left)
    if possible and not safe(automaton, usual, budget):
        counts['usual fails'] += 1
    # Proposition 4.1: masks from the distance in characters
    if set(letters) <= set(tokens) and possible:
        upper = lambda q, left: [t for t in tokens if by_letter.get(step(automaton, q, t), FAR) <= left - 1]
        lower = lambda q, left: [t for t in tokens if step(automaton, q, t) in by_letter
                                 and math.ceil(by_letter[step(automaton, q, t)] / longest) <= left - 1]
        counts['with letters'] += 1
        if by_letter[start] <= budget:
            assert safe(automaton, upper, budget), 'the mask by characters fails although every character is a token'
        counts['upper loses'] += outputs(automaton, far, upper, budget) != wanted
        counts['lower fails'] += not safe(automaton, lower, budget)
    # Theorems 6.1 and 6.2: a budget in another unit, and two budgets at once
    price = {token: rng.randrange(1, 4) for token in tokens}
    purse = rng.randrange(0, 6)
    cost = priced_distance(automaton, tokens, price)
    least = within(automaton, tokens, price, budget)
    affordable = {chosen for size in range(purse + 1) for chosen in product(tokens, repeat=size)
                  if sum(price[t] for t in chosen) <= purse and accepts(automaton, start, ''.join(chosen))}
    both = {chosen for chosen in wanted if sum(price[t] for t in chosen) <= purse}
    for name, expected, fits, allowed in (
            ('one', affordable, cost.get(start, FAR) <= purse,
             lambda q, left, money, t: cost.get(step(automaton, q, t), FAR) <= money - price[t]),
            ('two', both, least[budget].get(start, FAR) <= purse,
             lambda q, left, money, t: left >= 1 and (cost if MUTANT == 'cheapest-only' else least[left - 1]).get(step(automaton, q, t), FAR) <= money - price[t])):
        found, todo = set(), [((), start, budget, purse)]
        while todo:
            said, q, left, money = todo.pop()
            if q in automaton['finals']:
                found.add(said)
            options = [t for t in tokens if allowed(q, left, money, t)]
            assert q in automaton['finals'] or options or not fits, 'a run with a budget in another unit fails'
            todo += [(said + (t,), step(automaton, q, t), left - 1, money - price[t]) for t in options]
        assert found == expected, 'the outputs with a budget in another unit are not the accepted sequences within it'
        assert fits == bool(expected), 'the check before the first token is wrong for a budget in another unit'
        counts['priced ' + name] += len(expected)
    counts['automata'] += 1


def random_pushdown(rng):
    letters = 'ab' if rng.random() < 0.5 else 'abc'
    n = rng.randrange(2, 4)
    symbols = ['A'] if rng.random() < 0.4 else ['A', 'B']
    moves = {}
    for q in range(n):
        for c in letters:
            for top in [''] + symbols:
                if rng.random() < 0.6:
                    what = rng.choice(('keep', 'keep', 'push', 'pop' if top else 'push'))
                    moves[q, c, top] = (rng.randrange(n), (what, rng.choice(symbols)) if what == 'push' else (what,))
    finals = {q for q in range(n) if rng.random() < 0.4} or {rng.randrange(n)}
    tokens = set()
    while len(tokens) < rng.randrange(2, 5):
        tokens.add(''.join(rng.choice(letters) for _ in range(rng.randrange(1, 3))))
    return dict(states=list(range(n)), symbols=symbols, moves=moves, finals=finals), sorted(tokens)


def check_pushdown(rng, counts):
    """Theorem 5.1 on one random pushdown schema, and Theorems 3.1 and 3.2 with its distance."""
    schema, tokens = random_pushdown(rng)
    far = summaries(schema, tokens)
    most = 5
    stacks = [stack for depth in range(4) for stack in product(schema['symbols'], repeat=depth)]
    for q in schema['states']:
        for stack in stacks:
            mine, forced = far((q, stack)), push_fewest(schema, tokens, (q, stack), most)
            assert forced == (mine if mine <= most else None), 'the distance of a configuration differs from the search'
            counts['configurations'] += 1
            counts['spanning'] += mine < FAR and bool(stack)
    budget = rng.randrange(1, 5)
    start = (0, ())
    wanted, runs, todo = set(), set(), [((), start, budget)]
    for size in range(budget + 1):
        for chosen in product(tokens, repeat=size):
            c = start
            for token in chosen:
                c = c and push_step(schema, c, token)
            if c and push_accepts(schema, c):
                wanted.add(chosen)
    while todo:
        said, c, left = todo.pop()
        if push_accepts(schema, c):
            runs.add(said)
        allowed = [t for t in tokens if left and push_step(schema, c, t) is not None and far(push_step(schema, c, t)) <= left - 1]
        assert push_accepts(schema, c) or allowed or far(start) > budget, 'a run of the pushdown decoder fails'
        assert far(start) > budget or len(c[1]) <= max(len(t) for t in tokens) * left, 'the stack is deeper than the budget can close'
        counts['deepest'] = max(counts['deepest'], len(c[1]) if far(start) <= budget else 0)
        todo += [(said + (t,), push_step(schema, c, t), left - 1) for t in allowed]
    assert runs == wanted, 'the outputs of the pushdown decoder are not the accepted sequences'
    counts['pushdown'] += 1


def catches(name):
    """The check that notices the mistake, or None."""
    global MUTANT
    MUTANT = name
    rng = random.Random(2026)
    counts = dict.fromkeys(FIELDS, 0)
    try:
        for _ in range(150):
            check_regular(rng, counts)
        for _ in range(40):
            check_pushdown(rng, counts)
        return None
    except AssertionError as failed:
        return str(failed) or 'a check without a name'
    finally:
        MUTANT = None


FIELDS = ('automata', 'dead', 'safe', 'outputs', 'forbidden', 'usual fails', 'with letters', 'upper loses', 'lower fails',
          'pushdown', 'configurations', 'spanning', 'deepest', 'priced one', 'priced two')

# The example of Section 5: a value is the letter a or a list of values in square brackets.
# The states: V a value must come, O a list was just opened, A a value has ended.
LISTS = dict(states=['V', 'O', 'A'], symbols=['L'], finals={'A'},
             moves={('V', 'a', ''): ('A', ('keep',)), ('V', '[', ''): ('O', ('push', 'L')),
                    ('V', 'a', 'L'): ('A', ('keep',)), ('V', '[', 'L'): ('O', ('push', 'L')),
                    ('O', 'a', 'L'): ('A', ('keep',)), ('O', '[', 'L'): ('O', ('push', 'L')), ('O', ']', 'L'): ('A', ('pop',)),
                    ('A', ',', 'L'): ('V', ('keep',)), ('A', ']', 'L'): ('A', ('pop',))})
LISTS_TOKENS = ['a', '[', ']', ',', '[[', ']]', '],[', 'a]', 'a,a']

# The example of Section 2: an object with a name and a list of tags, over the letters a and b.
EXAMPLE = r'\{"name":"[ab]+","tags":\[("[ab]+"(,"[ab]+")*)?\]\}'
EXAMPLE_TOKENS = sorted(set('{}[]",:abnmetgs') | {'{"', 'name', '":"', '","', 'tags', '":[', '"]}', '"]', ']}', '",',
                                                  'ab', 'ba', 'aa', 'bb', '"a', '"b', 'a"', 'b"'})


def simulate(rng, automaton, tokens, far, budget, runs):
    """A model that picks among what it may do with equal chances, under the usual mask and
    under the budget mask.  Returns how many runs under the usual mask end incomplete, how
    many runs under the budget mask the budget changed, the most tokens that were left when it
    did, and the share of steps at which the two masks differ."""
    cut = touched = earliest = steps = differ = 0
    alive = set(far)
    for _ in range(runs):
        q, left = automaton['start'], budget
        while left:
            choices = live_mask(automaton, tokens, alive, q, left) + (['stop'] if q in automaton['finals'] else [])
            token = rng.choice(choices)
            if token == 'stop':
                break
            q, left = step(automaton, q, token), left - 1
        cut += q not in automaton['finals']
        q, left, changed = automaton['start'], budget, False
        while left:
            mine = budget_mask(automaton, tokens, far, q, left)
            usual = live_mask(automaton, tokens, alive, q, left)
            steps += 1
            if mine != usual:
                differ += 1
                changed = True
                earliest = max(earliest, left)
            choices = mine + (['stop'] if q in automaton['finals'] else [])
            assert choices, 'the decoder has nothing to do'
            token = rng.choice(choices)
            if token == 'stop':
                break
            q, left = step(automaton, q, token), left - 1
        assert q in automaton['finals'], 'a run under the budget mask ends incomplete'
        touched += changed
    return cut, touched, earliest, differ / steps


def percent(part, whole):
    return f'{100 * part / whole:.0f}'


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten', 'eleven', 'twelve']

    # Section 2: the example
    automaton = compile_expression(EXAMPLE)
    far = distance(automaton, EXAMPLE_TOKENS)
    by_letter = distance(automaton, characters(automaton))
    start = automaton['start']
    shortest = '{"name":"a","tags":[]}'
    widest = max(far.values())
    claim('example', accepts(automaton, start, shortest) and by_letter[start] == len(shortest) and far[start] == 8
          and set(far) == set(by_letter) == set(automaton['states'])
          and accepts(automaton, start, ''.join(['{"', 'name', '":"', 'a', '","', 'tags', '":[', ']}']))
          and not accepts(automaton, start, '{"name":"ab","tags":["a') and widest == far[start] + 1)
    after = step(automaton, start, '{"name":"ab","tags":["a')
    claim('example-cut', far[after] == 1 and by_letter[after] == 3 and step(automaton, after, '"]}') in automaton['finals']
          and budget_mask(automaton, EXAMPLE_TOKENS, far, after, 1) == ['"]}']
          and sorted(budget_mask(automaton, EXAMPLE_TOKENS, far, after, 2)) == ['"', '"]', '"]}', 'a', 'a"', 'aa', 'ab', 'b', 'b"', 'ba', 'bb']
          and len(live_mask(automaton, EXAMPLE_TOKENS, set(far), after, 2)) == 13)
    said = ['{"', 'name', '":"', 'ab', '","', 'tags', '":[', '"a', 'b']
    tt = lambda token: '\\texttt{' + token.replace('{', '\\{').replace('}', '\\}') + '}'
    tables['trace'], q = [], start
    for i, token in enumerate(said):
        q = step(automaton, q, token)
        left = len(said) - i - 1
        tables['trace'].append(f"{i + 1} & {tt(token)} & {left} & {far[q]} & {by_letter[q]} & "
                               f"{'yes' if far[q] <= left else 'no'} \\\\")
    claim('example-trace', all(row.endswith('yes \\\\') for row in tables['trace'][:-1]) and tables['trace'][-1].endswith('no \\\\')
          and not accepts(automaton, start, ''.join(said)) and accepts(automaton, start, ''.join(said[:-1] + ['"]}'])))
    longest = max(len(token) for token in EXAMPLE_TOKENS)
    firsts = [step(automaton, start, token) for token in EXAMPLE_TOKENS if step(automaton, start, token) is not None]
    upper = lambda q, left: [t for t in EXAMPLE_TOKENS if by_letter.get(step(automaton, q, t), FAR) <= left - 1]
    lower = lambda q, left: [t for t in EXAMPLE_TOKENS if step(automaton, q, t) in by_letter
                             and math.ceil(by_letter[step(automaton, q, t)] / longest) <= left - 1]
    claim('example-characters', longest == 4 and upper(start, 9) == [] and min(by_letter[q] for q in firsts) == 20
          and math.ceil(by_letter[start] / longest) == 6 and lower(start, 5) == [] and '{"' in lower(start, 6)
          and '{"' in lower(start, 7) and far[start] > 7)
    lines.append(f"the example: {len(automaton['states'])} states, {len(EXAMPLE_TOKENS)} tokens; the shortest output has "
                 f"{by_letter[start]} characters and {far[start]} tokens; no state is further than {widest} tokens from the end")
    nums.update(ExampleStates=str(len(automaton['states'])), ExampleTokens=str(len(EXAMPLE_TOKENS)),
                ExampleCharacters=str(by_letter[start]), ExampleFar=spelled[far[start]], ExampleWidest=spelled[widest])

    # Section 5: lists of lists
    far_lists = summaries(LISTS, LISTS_TOKENS)
    tables['lists'] = []
    for depth in range(7):
        stack = ('L',) * depth
        found = {state: far_lists((state, stack)) for state in ('A', 'O', 'V')}
        for state, value in found.items():
            assert push_fewest(LISTS, LISTS_TOKENS, (state, stack), 7) == (value if value <= 7 else None), 'lists'
        show = lambda value: '--' if value == FAR else str(value)
        tables['lists'].append(f"{depth} & {show(found['A'])} & {show(found['O'])} & {show(found['V'])} \\\\")
    deepest = {}
    for budget in (2, 4, 6):
        seen, todo, deep = set(), [(('V', ()), budget)], 0
        while todo:
            c, left = todo.pop()
            if (c, left) in seen:
                continue
            seen.add((c, left))
            deep = max(deep, len(c[1]))
            todo += [(push_step(LISTS, c, t), left - 1) for t in LISTS_TOKENS
                     if left and push_step(LISTS, c, t) is not None and far_lists(push_step(LISTS, c, t)) <= left - 1]
        deepest[budget] = deep
    claim('lists', all(far_lists(('A', ('L',) * k)) == (k + 1) // 2 for k in range(7))
          and all(far_lists(('O', ('L',) * k)) == (k + 1) // 2 for k in range(1, 7))
          and all(far_lists(('V', ('L',) * k)) == 1 + k // 2 for k in range(7))
          and far_lists(('O', ())) == FAR and deepest == {2: 2, 4: 4, 6: 6})
    lines.append('lists of lists: with k brackets open the end is (k + 1) // 2 tokens away after a value, and 1 + k // 2 before one; '
                 f'with a budget of 2, 4, 6 tokens the decoder opens at most {deepest[2]}, {deepest[4]}, {deepest[6]} brackets')

    # a vocabulary that cannot spell what the schema asks for
    small = compile_expression('ab')
    words = ['a', 'ab', 'bb']
    far_small = distance(small, words)
    middle = step(small, 0, 'a')
    claim('stuck', far_small[0] == 1 and middle not in far_small and middle in distance(small, ['a', 'b'])
          and not safe(small, lambda q, left: live_mask(small, words, set(distance(small, ['a', 'b'])), q, left), 3)
          and safe(small, lambda q, left: budget_mask(small, words, far_small, q, left), 3)
          and budget_mask(small, words, far_small, 0, 3) == ['ab'])
    lines.append('the schema ab with the tokens a, ab, bb: after a the usual mask has no token; the budget mask allows only ab')

    # random automata and vocabularies
    counts = dict.fromkeys(FIELDS, 0)
    for _ in range(5000):
        check_regular(rng, counts)
    claim('regular', counts['automata'] == 5000 and counts['safe'] > 500 and counts['forbidden'] > 1000 and counts['dead'] > 0
          and counts['usual fails'] > 0)
    claim('characters', counts['upper loses'] > 0 and counts['lower fails'] > 0)
    claim('priced', counts['priced one'] > 1000 and counts['priced two'] > 1000)
    lines.append(f"{counts['automata']} random automata and vocabularies: the distance in tokens is what trying every sequence gives; "
                 f"with enough budget ({counts['safe']} cases) no run under the budget mask fails; its outputs are the "
                 f"{counts['outputs']} accepted sequences within the budget; each of the {counts['forbidden']} tokens it forbids has no "
                 f"completion in what is left; far from the end it is the usual mask; {counts['dead']} states can be completed by "
                 f"characters and not by tokens; the usual mask has a failing run in {counts['usual fails']} cases")
    lines.append(f"of {counts['with letters']} cases in which every character is a token and the budget suffices: the mask by "
                 f"characters loses outputs in {counts['upper loses']}; the mask by characters over the longest token fails in "
                 f"{counts['lower fails']}")
    lines.append(f"with prices for the tokens: the decoder with a budget in that unit has exactly the {counts['priced one']} "
                 f"accepted sequences within it as outputs, and with a budget in tokens as well exactly the {counts['priced two']} "
                 f"within both; no run fails where an output fits")
    nums.update(PricedOne=f"{counts['priced one']:,}", PricedTwo=f"{counts['priced two']:,}")
    nums.update(Automata=f"{counts['automata']:,}", Safe=f"{counts['safe']:,}", Outputs=f"{counts['outputs']:,}",
                Forbidden=f"{counts['forbidden']:,}", Dead=f"{counts['dead']:,}", UsualFails=f"{counts['usual fails']:,}",
                WithLetters=f"{counts['with letters']:,}", UpperLoses=f"{counts['upper loses']:,}",
                LowerFails=f"{counts['lower fails']:,}")

    # pushdown schemas
    for _ in range(600):
        check_pushdown(rng, counts)
    claim('nested', counts['pushdown'] == 600 and counts['spanning'] > 500 and counts['deepest'] > 1)
    lines.append(f"{counts['pushdown']} random pushdown schemas, {counts['configurations']} configurations with up to three symbols on "
                 f"the stack: the distance from summaries is what the search gives ({counts['spanning']} with a stack have a "
                 f"completion); the decoder never fails within its budget, its outputs are the accepted sequences, and its stack is never deeper than "
                 f"the budget can close (it gets {counts['deepest']} deep)")
    nums.update(Pushdown=str(counts['pushdown']), Configurations=f"{counts['configurations']:,}", Spanning=f"{counts['spanning']:,}")

    # the example with a model that picks at random
    tables['runs'] = []
    runs, results = 2000, {}
    for extra in (0, 2, 4, 8, 16, 32):
        budget = far[start] + extra
        cut, touched, earliest, differ = simulate(rng, automaton, EXAMPLE_TOKENS, far, budget, runs)
        results[extra] = (cut, touched, earliest)
        tables['runs'].append(f"{budget} & {percent(cut, runs)} & 0 & {percent(touched, runs)} & {100 * differ:.0f} & {earliest} \\\\")
        lines.append(f"budget {budget}: of {runs} runs under the usual mask {cut} end incomplete; under the budget mask none does, "
                     f"the budget changes {touched} runs, at most {earliest} tokens before the end")
    claim('runs', all(cut > 0 and earliest <= widest for cut, touched, earliest in results.values())
          and results[0][0] > results[32][0] and results[0][1] == runs)
    nums.update(Runs=f"{runs:,}", CutTight=percent(results[0][0], runs),                 CutTightRuns=f"{results[0][0]:,}", CutLooseRuns=str(results[32][0]), TouchedLooseRuns=str(results[32][1]), BudgetLoose=str(far[start] + 32),
                BudgetTight=spelled[far[start]])

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed:')
    lines.extend(f'  {name}: {caught[name]}' for name in MUTANTS)
    nums.update(Mutants=spelled[len(MUTANTS)],
                Size=f"{round(len(open(os.path.join(here, 'budget.py')).readlines()), -2):,}")

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
        f.write('% written by budget.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by budget.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
