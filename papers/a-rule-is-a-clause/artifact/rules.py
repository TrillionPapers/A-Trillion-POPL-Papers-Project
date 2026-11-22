#!/usr/bin/env python3
"""Tests the claims of "A Rule Is a Clause" on an implementation of its analyses.

The file has seven parts.

1. Actions, patterns, rules and lists, and what a list decides.
2. The finite set of actions on which two lists agree if they agree anywhere (Lemma 3.1), and
   brute force over it.  Nothing else in the file is trusted: every analysis is compared with
   this.
3. Usefulness: is there an action that a pattern matches and that no row of a matrix matches?
   One pass for words from an open alphabet, a search for a closed one.
4. The four diagnoses of a list: dead, masked, redundant, undecided.
5. The decision tree of a list, its reduced form, equivalence, and the normal form of a list of
   prefix patterns.
6. Lists that grow by hand, and the reduction from satisfiability.
7. The tests.  `python3 rules.py out` writes out/check.txt, out/numbers.tex and the tables.

A test is not a proof.  The proofs are in the paper.
"""
import os
import random
import sys
from itertools import product

MUTANT = None       # one of MUTANTS: a deliberate mistake that the tests must notice
CLAIMS = set()      # the sentences of the paper, by name, that this run has checked
ANY = None          # the pattern for one word, whatever it is
FRESH = '~'         # a word that no rule mentions


def claim(name, holds):
    """The paper marks a sentence that states a fact in words with \\claim{name}{...}.  Every
    such sentence has one call of this function, and main() compares the two sets of names."""
    assert holds, name
    CLAIMS.add(name)


# ---------------------------------------------------------------------------------------------
# 1. An action is (tool, words).  A pattern is (tool, items, rest): every item is a word or ANY,
#    and rest says whether more words may follow.  A rule is (pattern, decision).  A list is its
#    rules in order and the decision for an action that no rule matches.
# ---------------------------------------------------------------------------------------------

DECISIONS = ('allow', 'ask', 'deny')


def matches(pattern, action):
    tool, items, rest = pattern
    name, words = action
    if tool != name or len(words) < len(items) or (len(words) > len(items) and not rest):
        return False
    return all(item is ANY or item == word for item, word in zip(items, words)) and (rest or len(words) == len(items))


def first(rules, action):
    """The index of the first rule that matches, or None."""
    for index, (pattern, _) in enumerate(rules):
        if matches(pattern, action):
            return index
    return None


def decide(rules, default, action):
    index = first(rules, action)
    return default if index is None else rules[index][1]


def by_class(rules):
    """The order of a harness in which a denial beats a question and a question beats a
    permission, wherever the rules stand: the same rules, sorted by decision, each class in its
    own order."""
    rank = {'deny': 0, 'ask': 1, 'allow': 2}
    return sorted(rules, key=lambda rule: rank[rule[1]])


def show(pattern):
    tool, items, rest = pattern
    return f"{tool}({' '.join(['_' if item is ANY else item for item in items] + (['*'] if rest else []))})"


def parse(text):
    """`Bash(git push *)` and the like."""
    tool, _, inside = text.partition('(')
    parts = inside.rstrip(')').split()
    rest = bool(parts) and parts[-1] == '*'
    return (tool, tuple(ANY if part == '_' else part for part in (parts[:-1] if rest else parts)), rest)


# ---------------------------------------------------------------------------------------------
# 2. Lemma 3.1.  Replace every word that no pattern mentions by one fresh word, and cut an action
#    after one word more than the longest pattern has: the same patterns match.  So the actions
#    below, finitely many, stand for all.
# ---------------------------------------------------------------------------------------------

def universe(patterns, tools=(), alphabet=None):
    """Every action over the tools and words of the patterns, with one fresh word unless the
    alphabet is closed, up to one word more than the longest pattern."""
    names = sorted({tool for tool, _, _ in patterns} | set(tools))
    words = sorted({item for _, items, _ in patterns for item in items if item is not ANY})
    words = sorted(alphabet) if alphabet is not None else words + [FRESH]
    longest = max((len(items) for _, items, _ in patterns), default=0) + 1
    for name in names:
        for length in range(longest + 1):
            for chosen in product(words, repeat=length):
                yield (name, chosen)


# ---------------------------------------------------------------------------------------------
# 3. Usefulness.  The rows are patterns and q is a pattern: is there an action that q matches and
#    no row matches?  Over an open alphabet a fresh word is the best choice wherever q allows any
#    word, so one pass over the positions decides it.  Over a closed alphabet every word must be
#    tried.
# ---------------------------------------------------------------------------------------------

def useful(rows, q, alphabet=None):
    """A witness (an action) if there is one, else None."""
    tool, items, rest = q
    alive = [row for row in rows if row[0] == tool]

    def search(alive, position, words):
        # alive: the rows that match the words so far and want at least `position` words
        if any(r and len(i) <= position for _, i, r in alive) and MUTANT != 'no-rest':
            return None                                 # a row that takes all that follows
        alive = [row for row in alive if len(row[1]) >= position]
        if position >= len(items):
            if not any(len(i) == position for _, i, _ in alive):
                return (tool, tuple(words))             # stop here: nobody wants exactly this
            if not rest or MUTANT == 'end-covers':
                return None
            wanted, further = ANY, [row for row in alive if len(row[1]) > position]
        else:
            wanted, further = items[position], [row for row in alive if len(row[1]) > position]
        if wanted is not ANY:
            return search([row for row in further if row[1][position] in (wanted, ANY)], position + 1, words + [wanted])
        if alphabet is None:
            if MUTANT == 'known-word':
                return search(further, position + 1, words + [FRESH])
            return search([row for row in further if row[1][position] is ANY], position + 1, words + [FRESH])
        for word in sorted(alphabet):
            found = search([row for row in further if row[1][position] in (word, ANY)], position + 1, words + [word])
            if found:
                return found
        return None

    return search(alive, 0, [])


def meet(p, q):
    """The pattern for the actions that both match, or None if there are none."""
    (tp, ip, rp), (tq, iq, rq) = p, q
    if tp != tq:
        return None
    if len(ip) > len(iq):
        (ip, rp), (iq, rq) = (iq, rq), (ip, rp)
    if len(ip) < len(iq) and not rp and MUTANT != 'meet-length':
        return None                                     # p wants an end where q wants a word
    items = []
    for a, b in zip(ip, iq):
        if a is not ANY and b is not ANY and a != b:
            return None
        items.append(b if a is ANY else a)
    return (tp, tuple(items) + tuple(iq[len(ip):]), rp and rq)


# ---------------------------------------------------------------------------------------------
# 4. The diagnoses.  A rule is dead if no action reaches it.  A dead rule is masked if some
#    action that it matches gets another decision than the rule's: it was meant to change
#    something and does not.  A live rule is redundant if the list decides the same without it.
#    An action is undecided if no rule matches it.
# ---------------------------------------------------------------------------------------------

def diagnose(rules, default, alphabet=None):
    patterns = [pattern for pattern, _ in rules]
    dead, masked, redundant = set(), set(), set()
    for i, (p, d) in enumerate(rules):
        if useful(patterns[:i], p, alphabet) is None:
            dead.add(i)
            for j in range(i):
                both = meet(p, patterns[j])
                if rules[j][1] != d and both is not None and useful(patterns[:j], both, alphabet):
                    masked.add(i)
                    break
            continue
        others = patterns[:i] + patterns[i + 1:]
        changed = default != d and MUTANT != 'no-default' and useful(others, p, alphabet)
        for k in range(i + 1, len(rules)):
            both = meet(p, patterns[k])
            if changed or (rules[k][1] != d and both is not None
                           and useful(patterns[:i] + patterns[i + 1:k], both, alphabet)):
                changed = True
                break
        if not changed:
            redundant.add(i)
    tools = sorted({tool for tool, _, _ in patterns})
    undecided = [witness for witness in (useful(patterns, (tool, (), True), alphabet) for tool in tools) if witness]
    return dead, masked, redundant, undecided


STRICT = {'allow': 0, 'ask': 1, 'deny': 2}


def loosened(rules, alphabet=None):
    """The dead rules some of whose actions get a less strict decision than the rule's."""
    patterns = [pattern for pattern, _ in rules]
    result = set()
    for i, (p, d) in enumerate(rules):
        if useful(patterns[:i], p, alphabet) is None:
            for j in range(i):
                both = meet(p, patterns[j])
                if STRICT[rules[j][1]] < STRICT[d] and both is not None and useful(patterns[:j], both, alphabet):
                    result.add(i)
                    break
    return result


def loosened_by_force(rules, default):
    actions = list(universe([pattern for pattern, _ in rules]))
    reached = {first(rules, action) for action in actions}
    return {i for i, (p, d) in enumerate(rules) if i not in reached
            and any(matches(p, a) and STRICT[decide(rules, default, a)] < STRICT[d] for a in actions)}


def diagnose_by_force(rules, default, alphabet=None):
    """The same four answers from the definitions, by trying every action of the universe."""
    patterns = [pattern for pattern, _ in rules]
    actions = list(universe(patterns, alphabet=alphabet))
    reached = {first(rules, action) for action in actions}
    dead = {i for i in range(len(rules)) if i not in reached}
    masked = {i for i in dead if any(matches(patterns[i], a) and decide(rules, default, a) != rules[i][1] for a in actions)}
    redundant = {i for i in range(len(rules)) if i not in dead
                 and all(decide(rules[:i] + rules[i + 1:], default, a) == decide(rules, default, a) for a in actions)}
    undecided = {tool for tool in {t for t, _, _ in patterns} if any(a[0] == tool and None is first(rules, a) for a in actions)}
    return dead, masked, redundant, undecided


def differ(rules1, default1, rules2, default2):
    """An action that the two lists decide differently, or None (Theorem 5.4): one question of
    usefulness for every pair of rules with different decisions, and for every rule and the
    other list's default.  No tree is built."""
    first_, second = [pattern for pattern, _ in rules1], [pattern for pattern, _ in rules2]
    for i, (p, d) in enumerate(rules1):
        if d != default2:                               # reaches rule i there, no rule here
            witness = useful(first_[:i] + second, p)
            if witness:
                return witness
        for j, (q, e) in enumerate(rules2):
            both = meet(p, q)
            if d != e and both is not None:             # reaches rule i there and rule j here
                witness = useful(first_[:i] + second[:j], both)
                if witness:
                    return witness
    for j, (q, e) in enumerate(rules2):
        if e != default1 and MUTANT != 'one-sided':     # reaches rule j here, no rule there
            witness = useful(second[:j] + first_, q)
            if witness:
                return witness
    if default1 != default2:                            # no rule of either list
        for tool in sorted({pattern[0] for pattern in first_ + second}):
            witness = useful(first_ + second, (tool, (), True))
            if witness:
                return witness
    return None


# ---------------------------------------------------------------------------------------------
# 5. The decision tree of the rules for one tool.  A node stands for the words read so far.  It
#    says which rule decides if the action ends here, has a child for every word that some rule
#    asks for next, and a child for every other word.  A leaf says which rule decides whatever
#    follows.  `floor` is the first rule on the way that takes all that follows: only rules
#    before it still matter.
# ---------------------------------------------------------------------------------------------

def tree(rules, tool):
    rows = [(index, pattern[1], pattern[2]) for index, (pattern, _) in enumerate(rules) if pattern[0] == tool]

    def build(rows, position, floor):
        for index, items, rest in rows:
            if rest and len(items) <= position and (floor is None or (index > floor if MUTANT == 'floor-last' else index < floor)):
                floor = index
        rows = [row for row in rows if floor is None or row[0] < floor]
        here = min([index for index, items, _ in rows if len(items) == position] + ([floor] if floor is not None else []),
                   default=None)
        deeper = [row for row in rows if len(row[1]) > position]
        if not deeper:
            return ('leaf', floor) if here == floor else ('node', here, {}, ('leaf', floor))
        words = sorted({items[position] for _, items, _ in deeper if items[position] is not ANY})
        children = {word: build([row for row in deeper if row[1][position] in (word, ANY)], position + 1, floor)
                    for word in words}
        other = build([row for row in deeper if row[1][position] is ANY], position + 1, floor)
        return ('node', here, children, other)

    return build(rows, 0, None)


def reduced(node, rules, default):
    """The tree with decisions in place of rules, without a child that says what the child for
    other words says, and with a leaf in place of a node that says one thing.  Two lists decide
    alike on a tool exactly if their reduced trees for it are equal (Theorem 6.2)."""
    say = lambda index: default if index is None else rules[index][1]
    if node[0] == 'leaf':
        return ('leaf', say(node[1]))
    _, here, children, other = node
    other = reduced(other, rules, default)
    kept = {}
    for word, child in children.items():
        child = reduced(child, rules, default)
        if child != other or MUTANT == 'keep-all':
            kept[word] = child
    if not kept and other == ('leaf', say(here)):
        return other
    return ('node', say(here), tuple(sorted(kept.items())), other)


def lookup(node, words):
    """What a reduced tree says of the words."""
    for position, word in enumerate(words):
        if node[0] == 'leaf':
            return node[1]
        node = dict(node[2]).get(word, node[3])
    return node[1]


def same(rules1, default1, rules2, default2):
    """Whether the lists decide alike on the tools that they mention, by their reduced trees."""
    tools = {pattern[0] for pattern, _ in rules1 + rules2}
    return all(reduced(tree(rules1, tool), rules1, default1) == reduced(tree(rules2, tool), rules2, default2)
               for tool in tools)


def size(node):
    """The number of nodes and leaves of a tree."""
    if node[0] == 'leaf':
        return 1
    children = node[2].values() if isinstance(node[2], dict) else [child for _, child in node[2]]
    return 1 + size(node[3]) + sum(size(child) for child in children)


def pairs(n):
    """A list of n rules whose reduced tree has more than 2**n nodes: rule j allows the actions
    of 2n words that have the word `a` at the places j and n + j."""
    rules = []
    for j in range(n):
        items = [ANY] * (2 * n)
        items[j] = items[n + j] = 'a'
        rules.append((('Bash', tuple(items), False), 'allow'))
    return rules


def used(node):
    """The rules that decide something in a tree."""
    if node[0] == 'leaf':
        return {node[1]}
    return {node[1]} | used(node[3]) | set().union(*[used(child) for child in node[2].values()]) if node[2] else {node[1]} | used(node[3])


def normal(rules, default):
    """The smallest list of prefix patterns that decides like a list of prefix patterns
    (Theorem 6.3): a rule for all that follows a prefix where that differs from what holds
    around it, a rule for the prefix alone where that differs from what follows it, and the
    longer prefix first."""
    result = []
    for tool in sorted({pattern[0] for pattern, _ in rules}):
        def walk(node, prefix, around):
            if node[0] == 'leaf':
                if node[1] != around:
                    result.append(((tool, prefix, True), node[1]))
                return
            _, here, children, other = node
            assert other[0] == 'leaf', 'a list of prefix patterns has a leaf for the other words'
            below = other[1]
            for word, child in children:
                walk(child, prefix + (word,), below)
            if here != below and MUTANT != 'no-exact':
                result.append(((tool, prefix, False), here))
            if below != around:
                result.append(((tool, prefix, True), below))
        walk(reduced(tree(rules, tool), rules, default), (), default)
    return result


# ---------------------------------------------------------------------------------------------
# 6. Lists that grow, and formulas.
# ---------------------------------------------------------------------------------------------

COMMANDS = {'git': {'push': {'origin': {'main': {}, 'dev': {}}, '--force': {}}, 'pull': {}, 'commit': {}, 'status': {}},
            'npm': {'install': {}, 'test': {}, 'publish': {}},
            'rm': {'-rf': {}}, 'curl': {}, 'ls': {}}


def random_pattern(rng, wild=0.0, tool='Bash', depth=4):
    """A pattern along a path of the commands above: a prefix of the path, and then the end or
    whatever follows."""
    items, level = [], COMMANDS
    for _ in range(1 + int(rng.random() * depth)):
        if not level:
            break
        word = rng.choice(sorted(level))
        items.append(ANY if rng.random() < wild else word)
        level = level[word]
    return (tool, tuple(items), rng.random() < 0.7)


def random_list(rng, size, wild=0.0, tools=('Bash',)):
    rules = [(random_pattern(rng, wild, rng.choice(tools)), rng.choice(DECISIONS)) for _ in range(size)]
    return rules, rng.choice(DECISIONS)


def formula_rows(clauses, variables):
    """The reduction of Theorem 4.4.  An assignment is an action of one word for every variable,
    each 't' or 'f'.  The row for a clause matches the assignments that make the clause false.
    The pattern of any words is useful against the rows exactly if the formula can be
    satisfied."""
    rows = []
    for clause in clauses:
        items = [ANY] * variables
        for literal in clause:
            items[abs(literal) - 1] = 'f' if literal > 0 else 't'
        rows.append(('Opt', tuple(items), False))
    return rows, ('Opt', (ANY,) * variables, False)


def satisfiable(clauses, variables):
    return any(all(any((literal > 0) == bits[abs(literal) - 1] for literal in clause) for clause in clauses)
               for bits in product((False, True), repeat=variables))


# ---------------------------------------------------------------------------------------------
# 7. The tests.
# ---------------------------------------------------------------------------------------------

# The list of Section 2, as an operator might have written it over a year.
EXAMPLE = [('Bash(git status)', 'allow'), ('Bash(git *)', 'ask'), ('Bash(git push --force *)', 'deny'),
           ('Bash(npm test)', 'allow'), ('Bash(npm *)', 'ask'), ('Bash(npm test)', 'allow'),
           ('Bash(rm -rf *)', 'deny'), ('Bash(rm *)', 'ask'), ('Bash(ls *)', 'allow'),
           ('Read(src *)', 'allow'), ('Read(src secrets *)', 'deny'), ('Read(_ README.md)', 'allow'),
           ('Bash(git pull)', 'ask')]
EXAMPLE_DEFAULT = 'ask'
MUTANTS = ('end-covers', 'no-rest', 'known-word', 'meet-length', 'no-default', 'one-sided', 'floor-last', 'keep-all', 'no-exact')


def one_round(rng, counts, wild=0.3):
    """One random list, every analysis against brute force."""
    rules, default = random_list(rng, 2 + int(rng.random() * 7), wild, tools=('Bash', 'Read') if rng.random() < 0.3 else ('Bash',))
    patterns = [pattern for pattern, _ in rules]
    actions = list(universe(patterns))
    # usefulness: every rule against the rules before it
    for i, pattern in enumerate(patterns):
        witness = useful(patterns[:i], pattern)
        by_force = any(first(rules, action) == i for action in actions)
        assert (witness is not None) == by_force, 'usefulness differs from brute force'
        assert witness is None or (matches(pattern, witness) and first(rules, witness) == i), 'the witness is not one'
    # the meet of two patterns
    for p in patterns[:4]:
        for q in patterns[:4]:
            both = meet(p, q)
            for action in actions:
                assert (both is not None and matches(both, action)) == (matches(p, action) and matches(q, action)), 'the meet is wrong'
    dead, masked, redundant, undecided = diagnose(rules, default)
    fdead, fmasked, fredundant, fundecided = diagnose_by_force(rules, default)
    assert dead == fdead, 'dead rules differ from brute force'
    assert masked == fmasked, 'masked rules differ from brute force'
    assert redundant == fredundant, 'redundant rules differ from brute force'
    loose = loosened(rules)
    assert loose == loosened_by_force(rules, default), 'loosened rules differ from brute force'
    counts['loose'] += len(loose)
    assert {witness[0] for witness in undecided} == fundecided, 'undecided actions differ from brute force'
    assert all(first(rules, witness) is None for witness in undecided), 'an undecided action is decided'
    # the tree decides like the list, and its rules are the live ones
    live = set()
    for tool in {pattern[0] for pattern in patterns}:
        raw = tree(rules, tool)
        live |= used(raw) - {None}
        small = reduced(raw, rules, default)
        for name, words in actions:
            if name == tool:
                assert lookup(small, words) == decide(rules, default, (name, words)), 'the tree decides otherwise'
    assert live == set(range(len(rules))) - dead, 'the tree uses other rules than the live ones'
    # equivalence: the list without its dead rules, the list without one rule, and another list
    without = [rule for i, rule in enumerate(rules) if i not in dead]
    assert same(rules, default, without, default), 'the list without its dead rules decides otherwise'
    for i in range(len(rules)):
        gone = rules[:i] + rules[i + 1:]
        spare = i in dead or i in redundant
        assert same(rules, default, gone, default) == spare, 'the reduced trees differ from brute force'
        for one, two in ((rules, gone), (gone, rules)):
            witness = differ(one, default, two, default)
            assert (witness is None) == spare, 'equivalence by usefulness differs from brute force'
            assert witness is None or decide(one, default, witness) != decide(two, default, witness), 'the difference is none'
        counts['spare'] += spare
        counts['needed'] += not spare
    other, other_default = random_list(rng, 2 + int(rng.random() * 5), wild)
    alike = all(decide(rules, default, a) == decide(other, other_default, a)
                for a in universe(patterns + [pattern for pattern, _ in other]))
    assert same(rules, default, other, other_default) == alike, 'the reduced trees differ from brute force'
    witness = differ(rules, default, other, other_default)
    assert (witness is None) == alike, 'equivalence by usefulness differs from brute force'
    assert witness is None or decide(rules, default, witness) != decide(other, other_default, witness), 'the difference is none'
    counts['lists'] += 1
    counts['rules'] += len(rules)
    counts['actions'] += len(actions)
    counts['dead'] += len(dead)
    counts['masked'] += len(masked)
    counts['redundant'] += len(redundant)
    counts['alike'] += alike


def prefix_round(rng, counts):
    """One random list of prefix patterns and its normal form."""
    rules, default = random_list(rng, 1 + int(rng.random() * 7))
    short = normal(rules, default)
    assert same(rules, default, short, default), 'the normal form decides otherwise'
    assert len(short) <= len(rules), 'the normal form is longer'
    assert normal(short, default) == short, 'the normal form of a normal form is another list'
    assert {pattern for pattern, _ in short} <= {pattern for pattern, _ in rules}, 'the normal form has a pattern that the list has not'
    counts['prefix'] += 1
    counts['saved'] += len(rules) - len(short)
    counts['before'] += len(rules)


def smallest_by_force(rules, default, limit):
    """The least number of prefix rules, up to the limit, that decide like the list."""
    words = sorted({item for pattern, _ in rules for item in pattern[1]})
    tools = sorted({pattern[0] for pattern, _ in rules})
    longest = max(len(pattern[1]) for pattern, _ in rules)
    candidates = [((tool, chosen, rest), decision) for tool in tools for length in range(longest + 1)
                  for chosen in product(words, repeat=length) for rest in (False, True) for decision in DECISIONS]
    actions = list(universe([pattern for pattern, _ in rules]))
    wanted = [decide(rules, default, action) for action in actions]
    for size in range(limit + 1):
        for chosen in product(candidates, repeat=size):
            if [decide(list(chosen), default, action) for action in actions] == wanted:
                return size
    return None


def growth(rng, sizes, runs=200):
    """Lists of each size, written one random rule at a time.  The rules are drawn alike, so it
    does not matter for the list as a whole at which end a new rule is put.  It matters for the
    new rule: put last, it may be dead on arrival; put first, it lives and may kill others."""
    table = {}
    for size in sizes:
        totals = dict(dead=0, masked=0, loose=0, redundant=0, rules=0, clean=0, arrival=0, arrival_loose=0, killed=0)
        for _ in range(runs):
            rules = [(random_pattern(rng), rng.choice(DECISIONS)) for _ in range(size)]
            dead, masked, redundant, _ = diagnose(rules, 'ask')
            loose = loosened(rules)
            totals['dead'] += len(dead)
            totals['masked'] += len(masked)
            totals['loose'] += len(loose)
            totals['redundant'] += len(redundant)
            totals['rules'] += size
            totals['clean'] += not dead and not redundant
            totals['arrival'] += size - 1 in dead           # the rule that was put last
            totals['arrival_loose'] += size - 1 in loose
            patterns = [pattern for pattern, _ in rules]    # the rules that the first one kills
            totals['killed'] += sum(i in dead and useful(patterns[1:i], patterns[i]) is not None for i in range(1, size))
        table[size] = totals
    return table


FIELDS = ('lists', 'rules', 'actions', 'dead', 'masked', 'loose', 'redundant', 'alike', 'spare', 'needed', 'prefix', 'saved', 'before')


def catches(name):
    """The check that notices the mistake, or None."""
    global MUTANT
    MUTANT = name
    rng, counts = random.Random(2026), dict.fromkeys(FIELDS, 0)
    try:
        for _ in range(120):
            one_round(rng, counts)
            prefix_round(rng, counts)
        return None
    except AssertionError as failed:
        return str(failed) or 'a check without a name'
    finally:
        MUTANT = None


def percent(part, whole):
    return f'{100 * part / whole:.0f}'


def main(outdir):
    lines, nums, tables = [], {}, {}
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(2026)
    spelled = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten', 'eleven', 'twelve', 'thirteen']

    # Section 2: the list that rotted
    rules = [(parse(text), decision) for text, decision in EXAMPLE]
    dead, masked, redundant, undecided = diagnose(rules, EXAMPLE_DEFAULT)
    assert (dead, masked, redundant) == diagnose_by_force(rules, EXAMPLE_DEFAULT)[:3]
    short = normal([rule for rule in rules if rule[0][0] == 'Bash'], EXAMPLE_DEFAULT)
    bash = sum(rule[0][0] == 'Bash' for rule in rules)
    claim('example', dead == {2, 5, 10, 12} and masked == {2, 10} == loosened(rules) and redundant == {4, 7}
          and len(short) == bash - 6
          and decide(rules, EXAMPLE_DEFAULT, ('Bash', ('git', 'push', '--force', 'origin'))) == 'ask'
          and decide(rules, EXAMPLE_DEFAULT, ('Read', ('src', 'secrets', 'key'))) == 'allow'
          and {witness[0] for witness in undecided} == {'Bash', 'Read'})
    # the same list as a harness reads it in which a denial beats a question beats a permission
    ordered = by_class(rules)
    place = [i for i in sorted(range(len(rules)), key=lambda i: ({'deny': 0, 'ask': 1, 'allow': 2}[rules[i][1]], i))]
    assert [rules[i] for i in place] == ordered
    cdead, cmasked, credundant, _ = diagnose(ordered, EXAMPLE_DEFAULT)
    assert (cdead, cmasked, credundant) == diagnose_by_force(ordered, EXAMPLE_DEFAULT)[:3]
    cdead, cmasked, credundant = ({place[i] for i in found} for found in (cdead, cmasked, credundant))
    claim('example-classes', cdead == {0, 3, 5, 12} and cmasked == {0, 3, 5} and not loosened(ordered) and credundant == {7}
          and decide(ordered, EXAMPLE_DEFAULT, ('Bash', ('git', 'push', '--force', 'origin'))) == 'deny'
          and decide(ordered, EXAMPLE_DEFAULT, ('Read', ('src', 'secrets', 'key'))) == 'deny'
          and decide(ordered, EXAMPLE_DEFAULT, ('Bash', ('git', 'status'))) == 'ask'
          and decide(ordered, EXAMPLE_DEFAULT, ('Bash', ('npm', 'test'))) == 'ask')

    def notes(dead, masked, redundant):
        found = {i: 'dead, masked' for i in masked}
        found.update({i: 'dead' for i in dead - masked})
        found.update({i: 'redundant' for i in redundant})
        return found

    written, classes = notes(dead, masked, redundant), notes(cdead, cmasked, credundant)
    tables['example'] = []
    for i, (text, decision) in enumerate(EXAMPLE):
        tables['example'].append(f'{i + 1} & \\texttt{{{text.replace("_", chr(92) + "_").replace("--", "-{}-")}}} & {decision} & '
                                 f'{written.get(i, "")} & {classes.get(i, "")} \\\\')
    lines.append(f'the list of Section 2: dead {sorted(i + 1 for i in dead)}, masked {sorted(i + 1 for i in masked)}, '
                 f'redundant {sorted(i + 1 for i in redundant)}, undecided for instance '
                 + ', '.join(show((tool, words, False)) for tool, words in undecided))
    lines.append(f'the same list in the order of classes: dead {sorted(i + 1 for i in cdead)}, masked '
                 f'{sorted(i + 1 for i in cmasked)}, redundant {sorted(i + 1 for i in credundant)}')
    lines.append(f'the {bash} rules for Bash in normal form: ' + '; '.join(f'{show(p)} {d}' for p, d in short))
    nums.update(ExampleRules=spelled[len(rules)], ExampleBash=spelled[bash], ExampleShort=spelled[len(short)])

    # Sections 4 to 6 against brute force
    counts = dict.fromkeys(FIELDS, 0)
    for _ in range(2500):
        one_round(rng, counts)
    claim('force', counts['lists'] == 2500 and counts['dead'] > 1000 and counts['masked'] > 100 and counts['redundant'] > 1000
          and 0 < counts['loose'] < counts['masked'] and 0 < counts['alike'] < counts['lists']
          and counts['spare'] == counts['dead'] + counts['redundant'] and counts['needed'] > 1000)
    lines.append(f"{counts['lists']} random lists with {counts['rules']} rules, tried on {counts['actions']} actions: "
                 f"usefulness, the meet, the four diagnoses, the tree and both tests of equivalence agree with brute force; "
                 f"{counts['dead']} rules are dead, {counts['masked']} of them masked, {counts['loose']} of those loosened, "
                 f"{counts['redundant']} rules redundant; a list and the list without one rule decide alike for "
                 f"{counts['spare']} rules and not for {counts['needed']}; "
                 f"{counts['alike']} of the pairs of random lists decide alike")
    nums.update(Lists=f"{counts['lists']:,}", Rules=f"{counts['rules']:,}", Actions=f"{counts['actions']:,}",
                Dead=f"{counts['dead']:,}", Masked=f"{counts['masked']:,}", Loose=f"{counts['loose']:,}",
                Redundant=f"{counts['redundant']:,}", Spare=f"{counts['spare']:,}", Needed=f"{counts['needed']:,}",
                Alike=f"{counts['alike']:,}")

    # Section 6: a list whose reduced tree is large, and whose questions stay small
    largest = 8
    nodes = {n: size(reduced(tree(pairs(n), 'Bash'), pairs(n), 'deny')) for n in range(1, largest + 1)}
    for n in range(1, largest + 1):
        rules = pairs(n)
        assert diagnose(rules, 'deny')[:3] == (set(), set(), set()), 'a rule of the list of pairs is dead or redundant'
        assert differ(rules, 'deny', rules[::-1], 'deny') is None, 'the list of pairs read backwards decides otherwise'
        assert differ(rules, 'deny', rules[1:], 'deny') is not None, 'the list of pairs without a rule decides alike'
    claim('blowup', all(nodes[n] > 2 ** n for n in nodes) and all(nodes[n + 1] > 2 * nodes[n] for n in range(1, largest)))
    lines.append('the reduced tree of the list of n pairs has ' + ', '.join(f'{nodes[n]}' for n in sorted(nodes))
                 + f' nodes for n = 1 to {largest}')
    nums.update(BlowupLargest=spelled[largest], BlowupNodes=f'{nodes[largest]:,}', BlowupPower=f'{2 ** largest}')

    # Theorem 6.3: the normal form of a list of prefix patterns
    for _ in range(3000):
        prefix_round(rng, counts)
    tiny = smaller = 0
    while tiny < 60:
        rules, default = random_list(rng, 1 + int(rng.random() * 3))
        words = {item for pattern, _ in rules for item in pattern[1]}
        if len(words) > 2 or max(len(pattern[1]) for pattern, _ in rules) > 2:
            continue
        short = normal(rules, default)
        if len(short) > 3:
            continue
        assert smallest_by_force(rules, default, len(short)) == len(short), 'a shorter list of prefix patterns exists'
        tiny += 1
        smaller += len(short) < len(rules)
    claim('normal', counts['prefix'] == 3000 and counts['saved'] > 0 and tiny == 60)
    lines.append(f"{counts['prefix']} random lists of prefix patterns: the normal form decides alike and has "
                 f"{percent(counts['saved'], counts['before'])} percent fewer rules; for {tiny} lists of at most three rules "
                 f"no shorter list of prefix patterns decides alike")
    nums.update(Prefix=f"{counts['prefix']:,}", Saved=percent(counts['saved'], counts['before']), Tiny=str(tiny))

    # Section 7: lists that grow by hand
    sizes = (4, 8, 16, 32)
    grown = growth(rng, sizes)
    tables['growth'] = []
    for size_ in sizes:
        a = grown[size_]
        tables['growth'].append(f"{size_} & {percent(a['dead'], a['rules'])} & {percent(a['masked'], a['rules'])} & "
                                f"{percent(a['loose'], a['rules'])} & {percent(a['redundant'], a['rules'])} & "
                                f"{percent(a['clean'], 200)} & {percent(a['arrival'], 200)} & "
                                f"{percent(a['arrival_loose'], 200)} & {a['killed'] / 200:.1f} \\\\")
        lines.append(f"lists of {size_} rules: dead {a['dead']}/{a['rules']}, masked {a['masked']}, loosened {a['loose']}, "
                     f"redundant {a['redundant']}, clean lists {a['clean']}/200; the rule that was put last is dead in "
                     f"{a['arrival']} lists and loosened in {a['arrival_loose']}; the first rule kills {a['killed']} rules")
    big, small = grown[32], grown[4]
    claim('growth', all(grown[s][key] / grown[s]['rules'] < grown[t][key] / grown[t]['rules']
                        for key in ('dead', 'masked', 'loose') for s, t in zip(sizes, sizes[1:]))
          and all(grown[s][key] < grown[t][key] for key in ('arrival', 'killed') for s, t in zip(sizes, sizes[1:]))
          and big['dead'] * 2 > big['rules'] and big['clean'] == 0 and big['arrival'] * 2 > 200
          and all(grown[s]['masked'] * 2 > grown[s]['dead'] for s in sizes))
    nums.update(GrowthDead=percent(big['dead'], big['rules']), GrowthArrival=percent(big['arrival'], 200),
                GrowthArrivalSmall=percent(small['arrival'], 200), GrowthArrivalLoose=percent(big['arrival_loose'], 200),
                GrowthKilled=f"{big['killed'] / 200:.1f}",
                GrowthSmallClean=percent(small['clean'], 200), GrowthRuns='200', GrowthLargest='32')

    # the order of classes: a denial first, then a question, then a permission
    never = allows = 0
    for _ in range(1000):
        rules, default = random_list(rng, 8)
        ordered = by_class(rules)
        dead = diagnose(ordered, default)[0]
        assert not loosened(ordered), 'a rule is loosened in the order of classes'
        allows += sum(decision == 'allow' for _, decision in ordered)
        never += sum(ordered[i][1] == 'allow' for i in dead)
    claim('classes', 0 < never < allows)
    lines.append(f'1000 lists of 8 rules in the order of classes: no rule is loosened; {never} of {allows} permissions permit nothing')
    nums.update(ClassNever=percent(never, allows), ClassLists='1,000')

    # Theorem 4.4: a closed alphabet
    formulas = agree = unsat = 0
    while formulas < 400:
        variables = 3 + int(rng.random() * 5)
        clauses = [tuple(rng.choice((1, -1)) * v for v in rng.sample(range(1, variables + 1), 3))
                   for _ in range(int(variables * (3.5 + rng.random() * 2)))]
        rows, q = formula_rows(clauses, variables)
        can = satisfiable(clauses, variables)
        assert (useful(rows, q, alphabet={'t', 'f'}) is not None) == can, 'the reduction is wrong'
        assert useful(rows, q) is not None, 'with an open alphabet a fresh word is always a witness'
        formulas += 1
        unsat += not can
    claim('closed', formulas == 400 and 0 < unsat < formulas)
    lines.append(f'{formulas} random formulas, {unsat} of which cannot be satisfied: the last rule of the list of the '
                 f'reduction is dead exactly for those, when the words are t and f only; with an open alphabet it is never dead')
    nums.update(Formulas=str(formulas), Unsat=str(unsat))

    # every deliberate mistake is noticed
    caught = {name: catches(name) for name in MUTANTS}
    claim('all-noticed', all(caught.values()))
    lines.append(f'{len(MUTANTS)} deliberate mistakes, each noticed:')
    lines.extend(f'  {name}: {caught[name]}' for name in MUTANTS)
    nums.update(Mutants=spelled[len(MUTANTS)],
                Size=f"{round(len(open(os.path.join(here, 'rules.py')).readlines()), -2):,}")

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
        f.write('% written by rules.py; do not edit\n')
        for name in sorted(nums):
            f.write(f'\\newcommand{{\\ex{name}}}{{{nums[name]}}}\n')
    for name, rows_ in tables.items():
        with open(f'{outdir}/{name}.tex', 'w') as f:
            f.write('% written by rules.py; do not edit\n' + '\n'.join(rows_) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'out')
