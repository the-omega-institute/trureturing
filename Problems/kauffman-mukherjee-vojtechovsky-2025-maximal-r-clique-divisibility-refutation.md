---
slug: kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-divisibility-refutation
bibkey: kauffman2026multivirtual
doi: 10.1016/j.jalgebra.2026.03.018
url: https://arxiv.org/abs/2504.09368v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24
---

# Kauffman–Mukherjee–Vojtěchovský Problem 5.24

## Problem

Printed page 21 of arXiv:2504.09368v1, section 5.5, states:

> Problem 5.24. Does there exist a finite connected rack Q and a maximal R-clique C of Q such that |C| does not divide |Q|?

The printed question is existential. The preregistered claim24 is its negation: every inclusion-maximal R-clique in every finite connected rack has cardinality dividing the carrier cardinality. The result refutes this universal divisibility assertion; it answers the printed existence question Yes.

## Motivation

The source presents this as one of several open problems about finite connected racks. The result settles the stated question with a finite conjugation-rack counterexample. Preregistration: https://github.com/the-omega-institute/trureturing/issues/9420.

## Gap

This is a first-tier externally named problem. The bounded literature checks recorded in issue #9420 and Library/Certificates/kauffman2026multivirtual.md found no settlement in the searched scope. The 2026-09-30 check of five citing arXiv TeX sources and MathDB is orchestrator-reported. It does not establish exhaustive publication priority.

The paper's Example 5.11 on printed page 18 already answers Problem 5.23 negatively: ConnectedQuandle(10,1) has [R_0,R_1] = [R_1,R_3] = 1 but [R_0,R_3] ≠ 1, and maximal R-cliques partition a rack exactly when R-commutation is transitive. This delivery does not claim a settlement of Problem 5.23.

## Route

Use the conjugation rack of the 70 three-cycles in S₇, indexed by Fin 70, with x ∗ y = y⁻¹xy. The subset {(1 2 3),(1 3 2),(4 5 6),(4 6 5)}, indexed by {40,45,2,4}, is an inclusion-maximal R-clique of size 4. Since 4 does not divide 70, result24 supplies the existence requested by Problem 5.24.

The right-rack convention is literal: every right translation x ↦ mul x y is bijective, and multiplication is right self-distributive. RCommute means pointwise commutation of right translations; it is not replaced by commutation of the corresponding group elements. IsRClique includes all pairs, including equal members. IsMaximalRClique uses inclusion, rather than maximum size.

Connected means that a finite word of right translations sends any x to any y. On a finite carrier each bijective right translation has finite order, so its inverse is a nonnegative power of that translation. Consequently positive words, allowing the empty word, give exactly the orbits of the right multiplication group from printed page 17. The proof supplies explicit forward and return words for every index.

Fintype provides the finite carrier, and Finset represents every subset of it. DecidableEq is classically available and imposes no extra mathematical restriction. There are no additional rack hypotheses.

## Falsifier

Failure of connectedness, pairwise R-commutation or inclusion-maximality, an incorrect carrier cardinality, or divisibility of 70 by 4 would invalidate this witness. The local checks in result24 discharge these conditions using the pointwise conjugation table, its injective permutation embedding, right-translation words, and finite clique tests.

## Evidence

`D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24` has Lean type `¬ claim24`. Its kernel-checked axiom closure is `propext`, `Classical.choice`, and `Quot.sound`. Finite tests use `decide +kernel`; no native-decide axiom is used. All intermediate proof steps are local haves. The 11 authored private definitions contain witness data; there are no authored private theorem or lemma declarations.

## Triage

`theorem`. The result settles Problem 5.24 as quoted from arXiv v1. Problem 5.25, minimality of the witness, and exhaustive classification of connected racks are outside this conclusion.

### What the settlement shows

- The universal divisibility assertion is false, which answers the printed existential Problem 5.24 Yes under its stated finite-rack and connectedness hypotheses. [proved: D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24]

- The witness is a connected, faithful quandle, so neither idempotence nor distinct right translations repairs divisibility. Its seventy three-cycles generate A₇ with trivial centre; R-commutation, group-element commutation and centralization of the class by the commutator give identical pairwise tests. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `group` output; output |Q|=70, |generated group|=2520, |centre|=1, connected=True, idempotent=True, distinct right translations=70, 0 discrepancies among 4900 pairs]

- On this class, two three-cycles commute precisely when they are equal, are inverses on the same support, or have disjoint supports. A maximal clique therefore contains both orientations on each of two disjoint three-point supports, leaving one point unused. The settling clique generates C₃ × C₃ of order nine, but only four elements of that subgroup belong to the three-cycle class: clique cardinality is an intersection size, not the subgroup order to which Lagrange's theorem applies. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `supports` output; output 0 support-rule discrepancies among 4900 pairs, 2 supports of size 3, 1 unused point, generated subgroup order=9, subgroup intersection with Q=4, 2520%9=0]

- All maximal cliques in this witness have size four, yet 70=4·17+2. The carrier counts both orientations on all thirty-five three-point supports, while each maximal clique selects only two supports. These equal clique sizes do not impose divisibility. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `cliques` output; output 35 supports, |Q|=70, 70 maximal cliques of size 4, 70%4=2]

- In the neighbouring three-cycle classes tested, equal size survives throughout, and divisibility survives at n=5,6,8,9; the n=7 case is the sole failure in this range. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `neighbours` output; output carrier sizes=(20,40,70,112,168), clique sizes=(2,4,4,4,6), clique counts=(10,10,70,280,280), carrier remainders=(0,0,2,0,0)]

- For every n≥5, do the maximal R-cliques in the S_n three-cycle class consist of both orientations on floor(n/3) disjoint supports, giving size 2·floor(n/3) and divisibility exactly when floor(n/3) divides binomial(n,3)? This would turn the finite witness into an arithmetic classification, but the general statement is not proved by this module. [open]

- For the finite affine families tested, a stronger conclusion survives: every maximal R-clique is a singleton, so equal size and divisibility all hold. The cyclic operation is x ∗ y = tx + (1−t)y on Z/n, with both t and 1−t units; the binary-vector operation is x ∗ y = Tx + (I−T)y, with T and I−T invertible. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `affine` output; output 67 cyclic models, 2 models on 4 points, 48 models on 8 points, all connected with only singleton maximal cliques]

- The refutation is compatible with Proposition 5.15 and Corollaries 5.18–5.19 in the witness: all seventy maximal cliques are proper trivial four-element subquandles with singleton internal orbits. The §5.5 family retains equal-size blocks and divisibility in every tested parameter case, so the settlement does not invalidate those finite instances of its construction. The largest witness ratio is 4/70=2/35, while the tested source-family ratio is exactly 1/3; neither exceeds the thresholds of 5.25. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `restrictions and source-family` output; output 70 trivial four-element restricted tables; 30 connected source-family cases, 3 blocks each, (carrier size, clique size)=(6,2),(12,4),(24,8),(48,16), ratios=2/35 and 1/3]

### Executable computations

Run this self-contained command with Python 3. It uses only the standard library and runs outside the repository. Permutations are forward-image tuples; `compose(a, b)` means a ∘ b. The conjugation table uses y⁻¹xy, and clique edges test the right translations pointwise. Assertions check the reported hypotheses. The finite computations below are separate from the Lean proofs and make no claim about untested parameters.

The `group` columns are carrier size, generated-group order, centre order and number of distinct right translations. The `cliques` columns are support count, carrier size and maximal-clique count. The four arrays on `neighbours` list carrier sizes, clique sizes, clique counts and carrier remainders in increasing n. The `affine` columns count cyclic models and binary models in dimensions 2 and 3. The `source-family` columns count all (m,e) cases and list (carrier size, clique size) for m=1,…,4. Its operation is exactly the three-case formula of arXiv v1 §5.5: the second coordinate is a, a XOR b, or a XOR b XOR e according as i−j is 0, 1, or 2 modulo 3.

```sh
cd /tmp && python3 - <<'PY'
from itertools import permutations, combinations, product
from collections import Counter
from math import gcd
from fractions import Fraction

def compose(a, b):
    return tuple(a[x] for x in b)

def inverse(a):
    return tuple(a.index(x) for x in range(len(a)))

def commute(a, b):
    return compose(a, b) == compose(b, a)

def orbit(seed, steps):
    seen, todo = {seed}, [seed]
    for x in todo:
        for f in steps:
            y = f(x)
            if y not in seen:
                seen.add(y); todo.append(y)
    return seen

def closure(gens):
    return orbit(tuple(range(len(gens[0]))),
                 [lambda x, g=g: compose(x, g) for g in gens])

def cliques(adj):
    out = []
    def visit(r, p, x):
        if not p and not x:
            out.append(frozenset(r)); return
        u = max(p | x, key=lambda v: len(p & adj[v]))
        for v in sorted(p - adj[u]):
            visit(r | {v}, p & adj[v], x & adj[v])
            p.remove(v); x.add(v)
    visit(set(), set(range(len(adj))), set())
    return out

def table_data(t, laws=False):
    n = len(t)
    r = [tuple(t[x][y] for x in range(n)) for y in range(n)]
    assert all(len(set(a)) == n for a in r)
    assert all(t[x][x] == x for x in range(n))
    assert len(orbit(0, [lambda x, a=a: a[x] for a in r])) == n
    if laws:
        assert all(t[t[x][y]][z] == t[t[x][z]][t[y][z]]
                   for x, y, z in product(range(n), repeat=3))
    adj = [{b for b in range(n) if a != b and commute(r[a], r[b])}
           for a in range(n)]
    return r, adj, cliques(adj)

def conjugation_data(q):
    index = {a: i for i, a in enumerate(q)}
    t = [[index[compose(compose(inverse(b), a), b)] for b in q] for a in q]
    r, adj, cs = table_data(t)
    return t, r, adj, cs

def three_cycles(n):
    out = []
    for a, b, c in combinations(range(n), 3):
        for i, j, k in ((a, b, c), (a, c, b)):
            p = list(range(n)); p[i], p[j], p[k] = j, k, i
            out.append(tuple(p))
    return sorted(out)

q = three_cycles(7)
t, r, adj, cs = conjugation_data(q)
g = closure(q)
centre = [a for a in g if all(commute(a, b) for b in q)]
supports = [frozenset(i for i, x in enumerate(a) if i != x) for a in q]
discrepancies = support_discrepancies = 0
for a, b in product(range(len(q)), repeat=2):
    c = compose(compose(compose(inverse(q[a]), inverse(q[b])), q[a]), q[b])
    tests = (commute(r[a], r[b]), commute(q[a], q[b]),
             all(commute(c, x) for x in q))
    discrepancies += len(set(tests)) != 1
    rule = supports[a] == supports[b] or supports[a].isdisjoint(supports[b])
    support_discrepancies += tests[0] != rule
print('group:', len(q), len(g), len(centre), len(set(r)),
      'connected=True, idempotent=True, discrepancies=', discrepancies,
      'pairs=', len(q)**2)
c = frozenset((40, 45, 2, 4))
assert c in cs
h = closure([q[x] for x in c])
chosen = {supports[x] for x in c}
print('supports:', support_discrepancies, 'discrepancies;', len(chosen),
      'supports of size', sorted({len(s) for s in chosen}),
      'unused=', 7-len(set().union(*chosen)), 'subgroup=', len(h),
      'intersection=', len(h & set(q)), 'group remainder=', len(g) % len(h))
print('cliques:', len(set(supports)), len(q), len(cs),
      'sizes=', sorted(set(map(len, cs))), 'remainder=', len(q) % len(c))
assert all(t[a][b] == a for c in cs for a, b in product(c, repeat=2))
assert all(len(c) < len(q) for c in cs)
print('restrictions:', len(cs), 'trivial four-element tables, internal orbit size=1, ratio=',
      Fraction(max(map(len, cs)), len(q)))
sizes, clique_sizes, counts, remainders = [], [], [], []
for n in range(5, 10):
    qq = three_cycles(n)
    _, _, _, cc = conjugation_data(qq)
    spectrum = set(map(len, cc)); assert len(spectrum) == 1
    k = spectrum.pop()
    sizes.append(len(qq)); clique_sizes.append(k); counts.append(len(cc))
    remainders.append(len(qq) % k)
print('neighbours:', sizes, clique_sizes, counts, remainders)

cyclic = binary = 0
binary_counts = []
for n in range(2, 21):
    for a in range(n):
        if gcd(a, n) == gcd(1-a, n) == 1:
            t = [[(a*x + (1-a)*y) % n for y in range(n)] for x in range(n)]
            _, _, cs = table_data(t, laws=True)
            assert all(len(c) == 1 for c in cs)
            cyclic += 1
for d in (2, 3):
    n, count = 1 << d, 0
    for columns in product(range(n), repeat=d):
        def linear(x):
            y = 0
            for k, column in enumerate(columns):
                if (x >> k) & 1: y ^= column
            return y
        image = [linear(x) for x in range(n)]
        if len(set(image)) != n or len({x ^ image[x] for x in range(n)}) != n:
            continue
        t = [[image[x] ^ y ^ image[y] for y in range(n)] for x in range(n)]
        _, _, cs = table_data(t, laws=True)
        assert all(len(c) == 1 for c in cs)
        count += 1
    binary_counts.append(count)
print('affine:', cyclic, binary_counts, 'connected, singleton cliques')
source_cases, source_sizes = 0, []
for m in range(1, 5):
    n = 1 << m
    for e in range(n):
        q = list(product(range(3), range(n)))
        index = {a: i for i, a in enumerate(q)}
        def operation(x, y):
            i, a = x; j, b = y
            d = (i-j) % 3
            return ((-i-j) % 3, a ^ (b if d else 0) ^ (e if d == 2 else 0))
        t = [[index[operation(x, y)] for y in q] for x in q]
        r, _, cs = table_data(t, laws=True)
        blocks = {frozenset(index[(i, a)] for a in range(n)) for i in range(3)}
        assert set(cs) == blocks and len(set(r)) == 3*n
        source_cases += 1
    source_sizes.append((3*n, n))
print('source-family:', source_cases, source_sizes,
      '3 blocks, connected quandle, distinct translations, ratio', Fraction(1, 3))
PY
```

Output:

```text
group: 70 2520 1 70 connected=True, idempotent=True, discrepancies= 0 pairs= 4900
supports: 0 discrepancies; 2 supports of size [3] unused= 1 subgroup= 9 intersection= 4 group remainder= 0
cliques: 35 70 70 sizes= [4] remainder= 2
restrictions: 70 trivial four-element tables, internal orbit size=1, ratio= 2/35
neighbours: [20, 40, 70, 112, 168] [2, 4, 4, 4, 6] [10, 10, 70, 280, 280] [0, 0, 2, 0, 0]
affine: 67 [2, 48] connected, singleton cliques
source-family: 30 [(6, 2), (12, 4), (24, 8), (48, 16)] 3 blocks, connected quandle, distinct translations, ratio 1/3
```

## ASSUMED-UNVERIFIED

The journal full text was not read. Equality of its numbering and wording with arXiv v1 is unverified; this dossier cites arXiv v1. Literature priority beyond the bounded searched scope is unverified. 逃逸审计未完成：no existing enrolled template directly supplies the faithful realization bridge for these typeclass-quantified universal rack claims; no Reg registration is delivered. This boundary is disclosed with issue #9420.
