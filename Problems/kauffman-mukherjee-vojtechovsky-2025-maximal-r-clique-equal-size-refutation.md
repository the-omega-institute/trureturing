---
slug: kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-equal-size-refutation
bibkey: kauffman2026multivirtual
doi: 10.1016/j.jalgebra.2026.03.018
url: https://arxiv.org/abs/2504.09368v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22
---

# Kauffman–Mukherjee–Vojtěchovský Problem 5.22

## Problem

Printed page 21 of arXiv:2504.09368v1, section 5.5, states:

> Problem 5.22. Do all maximal R-cliques in a finite connected rack have the same size?

The affirmative reading says that any two inclusion-maximal R-cliques C and D have equal cardinalities. The formal claim22 quantifies over every Q : Type with Fintype Q and DecidableEq Q, every binary operation mul, and both cliques, with IsRack mul and Connected mul as premises.

## Motivation

The source presents this as one of several open problems about finite connected racks. The result settles the stated question with a finite conjugation-rack counterexample. Preregistration: https://github.com/the-omega-institute/trureturing/issues/9420.

## Gap

This is a first-tier externally named problem. The bounded literature checks recorded in issue #9420 and Library/Certificates/kauffman2026multivirtual.md found no settlement in the searched scope. The 2026-09-30 check of five citing arXiv TeX sources and MathDB is orchestrator-reported. It does not establish exhaustive publication priority.

The paper's Example 5.11 on printed page 18 already answers Problem 5.23 negatively: ConnectedQuandle(10,1) has [R_0,R_1] = [R_1,R_3] = 1 but [R_0,R_3] ≠ 1, and maximal R-cliques partition a rack exactly when R-commutation is transitive. This delivery does not claim a settlement of Problem 5.23.

## Route

Use the conjugation rack of the 105 fixed-point-free involutions in S₈, indexed by Fin 105, with x ∗ y = y⁻¹xy. On points 0 through 7, let C₇ contain the seven translations x ↦ x XOR a for a = 1,…,7. Let C₉ contain the nine permutations pₐᵦ for a,b ∈ {1,2,3}, acting by x XOR a on the lower four-point block and by 4 + ((x−4) XOR b) on the upper block. Their index sets are {0,16,32,52,68,88,104} and {0,1,2,15,16,17,30,31,32}. Both are inclusion-maximal R-cliques; their cardinalities are 7 and 9. Problem 5.22 is answered No.

The right-rack convention is literal: every right translation x ↦ mul x y is bijective, and multiplication is right self-distributive. RCommute means pointwise commutation of right translations; it is not replaced by commutation of the corresponding group elements. IsRClique includes all pairs, including equal members. IsMaximalRClique uses inclusion, rather than maximum size.

Connected means that a finite word of right translations sends any x to any y. On a finite carrier each bijective right translation has finite order, so its inverse is a nonnegative power of that translation. Consequently positive words, allowing the empty word, give exactly the orbits of the right multiplication group from printed page 17. The proof supplies explicit forward and return words for every index.

Fintype provides the finite carrier, and Finset represents every subset of it. DecidableEq is classically available and imposes no extra mathematical restriction. There are no additional rack hypotheses.

## Falsifier

Either clique failing pairwise R-commutation or inclusion-maximality, the rack failing connectedness, or equality of the two cardinalities would invalidate this witness. The local checks in result22 discharge these conditions using the pointwise conjugation table, its injective permutation embedding, right-translation words, and finite clique tests.

## Evidence

`D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22` has Lean type `¬ claim22`. Its kernel-checked axiom closure is `propext`, `Classical.choice`, and `Quot.sound`. Finite tests use `decide +kernel`; no native-decide axiom is used. All intermediate proof steps are local haves. The 11 authored private definitions contain witness data; there are no authored private theorem or lemma declarations.

## Triage

`theorem`. The result settles Problem 5.22 as quoted from arXiv v1. Problem 5.25, minimality of the witness, and exhaustive classification of connected racks are outside this conclusion.

### What the settlement shows

- The universal equal-size assertion in Problem 5.22 is false under its stated finite-rack and connectedness hypotheses. [proved: D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22]

- The failure already occurs in a connected, faithful quandle, so restricting from racks to quandles or requiring distinct right translations does not repair it. The 105 fixed-point-free involutions generate A₈, whose centre is trivial; on this class R-commutation agrees exactly with group-element commutation, including the test that the group commutator centralizes the class. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `group` output; output |Q|=105, |generated group|=20160, |centre|=1, distinct right translations=105, connected=True, idempotent=True, 0 discrepancies among 11025 pairs]

- The two clique sizes arise from different maximal elementary abelian subgroup actions. The seven XOR translations generate (C₂)³ acting regularly on eight points; all seven nonidentity elements are fixed-point-free. The nine blockwise XOR permutations generate (C₂)⁴ acting on two four-point orbits; precisely nine of its fifteen nonidentity elements move every point. Each subgroup equals its centralizer in S₈, and its intersection with Q is the corresponding clique, explaining inclusion-maximality without forcing equal cardinalities. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `C7 and C9` output; output C7: subgroup order=8, orbit sizes=(8), centralizer orders=(8,7); C9: subgroup order=16, orbit sizes=(4,4), centralizer orders=(16,9); both groups have exponent 2]

- Connectedness of the carrier does not make the action on maximal cliques transitive. The complete clique spectrum has 30 seven-element cliques and 35 nine-element cliques; conjugation by the generated A₈ splits them into orbits of sizes 15, 15 and 35. Equal size survives within each such orbit and within each of the two cardinality families. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `cliques` output; output 65 maximal cliques, size histogram={7:30,9:35}, A8 orbit sizes by clique size={7:(15,15),9:(35)}]

- For the finite affine families tested, a stronger conclusion survives: every maximal R-clique is a singleton, so equal size and divisibility all hold. The cyclic operation is x ∗ y = tx + (1−t)y on Z/n, with both t and 1−t units; the binary-vector operation is x ∗ y = Tx + (I−T)y, with T and I−T invertible. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `affine` output; output 67 cyclic models, 2 models on 4 points, 48 models on 8 points, all connected with only singleton maximal cliques]

- Does the singleton conclusion extend to every finite connected affine quandle, and does requiring the right multiplication group to act transitively on maximal R-cliques give a useful general equal-size repair beyond the computed examples? These general statements have no proof in this module. [open]

- The paper's §5.5 construction retains the desired behavior in every tested parameter case: Q_m(e) has exactly the three coordinate blocks as maximal R-cliques, each of size 2^m, in a carrier of size 3·2^m. This supplies restricted positive cases of 5.22 and divisibility in 5.24; it also attains, without exceeding, the one-third ratio discussed in 5.25. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `source-family` output; output 30 parameter cases, (carrier size, clique size)=(6,2),(12,4),(24,8),(48,16), exactly 3 blocks and all right translations distinct in each case]

- The S₈ witness is compatible with the local conclusions of Proposition 5.15 and Corollaries 5.18–5.19: every maximal clique has restricted operation x ∗ y = x, is a proper subquandle, and has only singleton internal orbits. Thus the unequal sizes do not produce a failure of those subrack or disconnectedness conclusions. Its largest clique has ratio 9/105=3/35, below both thresholds in Problem 5.25, so this witness does not answer that neighbouring question. [computed: run the inline `cd /tmp && python3` reproduction in [Executable computations](#executable-computations), `restrictions` output; output 65 trivial restricted tables, internal orbit size=1, largest clique=9<35=105/3, ratio=3/35]

### Executable computations

Run this self-contained command with Python 3. It uses only the standard library and runs outside the repository. Permutations are forward-image tuples; `compose(a, b)` means a ∘ b. The conjugation table uses y⁻¹xy, and clique edges test the right translations pointwise. Assertions check the reported hypotheses. The finite computations below are separate from the Lean proofs and make no claim about untested parameters.

The `group` columns are carrier size, generated-group order, centre order and number of distinct right translations. The `C7`/`C9` columns are subgroup order, point-orbit sizes, centralizer order in S₈ and centralizer intersection size with Q. The `affine` columns count cyclic models and binary models in dimensions 2 and 3. The `source-family` columns count all (m,e) cases and list (carrier size, clique size) for m=1,…,4. Its operation is exactly the three-case formula of arXiv v1 §5.5: the second coordinate is a, a XOR b, or a XOR b XOR e according as i−j is 0, 1, or 2 modulo 3.

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

identity = tuple(range(8))
s8 = list(permutations(range(8)))
q = [a for a in s8 if all(a[x] != x and a[a[x]] == x for x in range(8))]
t, r, adj, cs = conjugation_data(q)
g = closure(q)
centre = [a for a in g if all(commute(a, b) for b in q)]
discrepancies = 0
for a, b in product(range(len(q)), repeat=2):
    c = compose(compose(compose(inverse(q[a]), inverse(q[b])), q[a]), q[b])
    tests = (commute(r[a], r[b]), commute(q[a], q[b]),
             all(commute(c, x) for x in q))
    discrepancies += len(set(tests)) != 1
print('group:', len(q), len(g), len(centre), len(set(r)),
      'connected=True, idempotent=True, discrepancies=', discrepancies,
      'pairs=', len(q)**2)
for label, generators in (
    ('C7', [tuple(x ^ a for x in range(8)) for a in range(1, 8)]),
    ('C9', [tuple((x ^ a) if x < 4 else 4 + ((x-4) ^ b) for x in range(8))
            for a, b in product(range(1, 4), repeat=2)])):
    h = closure(generators)
    unseen, sizes = set(range(8)), []
    while unseen:
        o = orbit(min(unseen), [lambda x, a=a: a[x] for a in h])
        unseen -= o; sizes.append(len(o))
    centralizer = {a for a in s8 if all(commute(a, b) for b in generators)}
    assert centralizer == h
    assert all(compose(a, a) == identity for a in h)
    c = frozenset(q.index(a) for a in generators)
    assert c in cs and set(generators) == h & set(q)
    print(label + ':', len(h), sorted(sizes), len(centralizer),
          len(centralizer & set(q)), 'exponent=2')
remaining, orbit_sizes = set(cs), {}
while remaining:
    c = min(remaining, key=lambda x: tuple(sorted(x)))
    o = orbit(c, [lambda c, a=a: frozenset(a[x] for x in c) for a in r])
    assert o <= set(cs)
    remaining -= o
    orbit_sizes.setdefault(len(c), []).append(len(o))
print('cliques:', len(cs), dict(sorted(Counter(map(len, cs)).items())),
      'orbits=', {k: sorted(v) for k, v in sorted(orbit_sizes.items())})
assert all(t[a][b] == a for c in cs for a, b in product(c, repeat=2))
assert all(len(c) < len(q) for c in cs)
print('restrictions:', len(cs), 'trivial tables, internal orbit size=1, largest=',
      max(map(len, cs)), 'threshold=', len(q)//3,
      'ratio=', Fraction(max(map(len, cs)), len(q)))

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
group: 105 20160 1 105 connected=True, idempotent=True, discrepancies= 0 pairs= 11025
C7: 8 [8] 8 7 exponent=2
C9: 16 [4, 4] 16 9 exponent=2
cliques: 65 {7: 30, 9: 35} orbits= {7: [15, 15], 9: [35]}
restrictions: 65 trivial tables, internal orbit size=1, largest= 9 threshold= 35 ratio= 3/35
affine: 67 [2, 48] connected, singleton cliques
source-family: 30 [(6, 2), (12, 4), (24, 8), (48, 16)] 3 blocks, connected quandle, distinct translations, ratio 1/3
```

## ASSUMED-UNVERIFIED

The journal full text was not read. Equality of its numbering and wording with arXiv v1 is unverified; this dossier cites arXiv v1. Literature priority beyond the bounded searched scope is unverified. 逃逸审计未完成：no existing enrolled template directly supplies the faithful realization bridge for these typeclass-quantified universal rack claims; no Reg registration is delivered. This boundary is disclosed with issue #9420.
