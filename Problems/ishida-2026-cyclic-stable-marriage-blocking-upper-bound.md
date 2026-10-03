---
slug: ishida-2026-cyclic-stable-marriage-blocking-upper-bound
bibkey: ishida2026shield
doi: 10.48550/arXiv.2609.17418
url: https://arxiv.org/abs/2609.17418v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.result
---

# Ishida's cyclic stable-marriage arc-lemma upper bound

## Problem

Yoshiteru Ishida, *A Quadratic Lower Bound for the Shield Number of the Stable Marriage
Problem: Rearrangement, Extremal Construction, and Biclique Realizability*,
arXiv:2609.17418v1, Section 7.1, p. 8:

> This statement does not assert that µ∗ is maximum-blocking; that is exactly the open
> arc-lemma upper-bound problem.

Conclusion, p. 10:

> It does not claim the exact Shield-Core equality for general n, a universal Hall-feasible
> biclique theorem, or the general upper bound β(C_n) ≤ ⌊(n − 1)²/4⌋.

The cyclic profile (1) on labels 0 through n−1 is
r_M(g,h) = (h−g) mod n + 1 and r_W(h,g) = n − (h−g) mod n.
Smaller ranks are preferred. A complete matching is a bijection μ from men to women;
(g,h) blocks it when both r_M(g,h) < r_M(g,μ(g)) and
r_W(h,g) < r_W(h,μ⁻¹(h)). Write B(μ) for the number of such ordered pairs and
β(C_n) for its maximum over matchings.

The quantified target is: for every natural n≥1 and every permutation μ of Fin n,
B(μ) ≤ (n−1)²/4, where the division is natural division, hence the floor.

## Motivation

This is a Tier-1 explicitly published open question, preregistered with its quantified
statement and literature reading in [issue #12486](https://github.com/the-omega-institute/trureturing/issues/12486).
Theorem 5.3 of the source supplies a matching attaining the target. The upper bound
therefore determines the cyclic-profile maximum and settles the second equality of
the Shield-Core conjecture. The first equality compares the cyclic profile with all
strict complete profiles and is a separate question.

## Gap

The source explicitly leaves the upper bound open. The preregistration records a bounded
literature and MathDB search without a prior settlement in the searched scope.
Repository and pinned-Mathlib searches for stable marriage, stable matching, blocking
pairs, permutation alignments and the modular-rank expression found no carrier of
this target. These searches do not establish exhaustive coverage or publication priority.

## Route

Put U = {i : i≤μ(i)} and W = {i : μ(i)<i}, with cardinalities k and q.
Translate the strict cyclic rank inequalities into inversions within U, inversions
within W, and mixed blocking pairs. Across any cut t, the number of permutation edges
starting below t and ending at or above t equals the number going in the other direction.
This follows by counting the labels below the cut before and after applying μ.

Applying cut balance at μ(j)+1 bounds the U inversions by one class of mixed nesting
pairs. Applying it at w bounds the W inversions plus q by a second class.
The two classes and the mixed blocking pairs partition W×U, giving B(μ)+q≤qk.
Since k+q=n and (k−q−1)²≥0, one obtains 4B(μ)≤(n−1)² and the floor bound.

## Falsifier

A size n≥1 and permutation μ with more than ⌊(n−1)²/4⌋ blocking pairs would refute
the statement. A discrepancy in the modular ranks, inverse matching, strict comparisons,
pair cardinality or natural-number floor would invalidate the correspondence to the source.

## Evidence

The module `D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound.lean`
proves `result : claim`. Its public definitions are `rM`, `rW`, `blocks`, `B` and `claim`.
All auxiliary indicators, cut counts and estimates occur inside the proof of `result`.
The source's construction lower bound is literature evidence, not an additional Lean theorem
in this module.

The finite computation below exhausts all permutations at each n≤9, uses the source
modular ranks directly, and also counts the maximizers and their downward-edge counts q.
It is independent supporting computation, not a premise of the universal proof.

```sh
python3 - <<'PY'
from itertools import permutations
for n in range(1, 10):
    rank = [[(h-g) % n for h in range(n)] for g in range(n)]
    best, count, qs = -1, 0, set()
    for p in permutations(range(n)):
        inv = [0] * n
        for g, h in enumerate(p):
            inv[h] = g
        b = sum(rank[g][h] < rank[g][p[g]] and rank[g][h] > rank[inv[h]][h]
                for g in range(n) for h in range(n))
        q = sum(p[i] < i for i in range(n))
        if b > best:
            best, count, qs = b, 1, {q}
        elif b == best:
            count += 1
            qs.add(q)
    print(n, best, count, sorted(qs))
PY
```

| n | maximum B | maximizing permutations | their q values |
| --- | --- | --- | --- |
| 1 | 0 | 1 | 0 |
| 2 | 0 | 2 | 0, 1 |
| 3 | 1 | 3 | 1 |
| 4 | 2 | 12 | 1, 2 |
| 5 | 4 | 20 | 2 |
| 6 | 6 | 100 | 2, 3 |
| 7 | 9 | 175 | 3 |
| 8 | 12 | 980 | 3, 4 |
| 9 | 16 | 1764 | 4 |

## Triage

`theorem`: the cyclic-profile upper bound is proved for every n≥1 and every complete matching.

### What the settlement shows

- **Proved in this module:** permutation cut balance and the two nesting estimates give
  B(μ)+q≤qk for the same matching μ. The decisive mechanism is the bijection's preservation
  of cut cardinality. The bound applies to all complete matchings in the specified cyclic
  profile, including fixed points, without any optimality or polarized-form assumption.
- **Proved, using the source's Theorem 5.3 as literature:** β(C_n)=⌊(n−1)²/4⌋ exactly.
  This is the second equality of the Shield-Core conjecture. The upper bound is kernel-checked
  here; the attaining construction and the resulting equality are not separately formalized
  in this module. The polarized matching is maximum-blocking, so the orbit in Proposition 7.1
  attains the cyclic maximum. The other unconditional theorems of the source retain their scope.
- **Computed:** exhaustive values through n=9 and the corresponding numbers and q values
  of maximizing permutations are given above, with their reproducing command.
- **Open:** a general structural classification of maximizing matchings and all equality
  cases of the individual nesting estimates. The small-n q data do not supply that classification.
- **Open:** σ(n)=β(C_n), the first Shield-Core equality, and a universal Hall-feasible biclique
  theorem for arbitrary strict complete profiles. Neither follows from this cyclic upper bound.
- **Literature:** Sylvie Corteel, *Crossings and alignments of permutations*,
  arXiv:math/0601469, Proposition 5, gives the crossing–alignment identity for permutations.
  The blocking-pair translation identifies the relevant alignment count. This module uses
  permutation cut balance directly and does not import or formalize that identity.
- **Open:** extension of the same estimate to preference profiles outside the cyclic ranks (1).
  Its proof uses the cyclic rank comparison and gives no assertion for arbitrary profiles.

## ASSUMED-UNVERIFIED

The broad external literature and MathDB searches recorded in #12486 are supplied by the
preregistration and have not been independently repeated by this implementation seat.
Their not-found result is confined to the searched scope. No exhaustive priority claim is made.
The cyclic upper bound does not certify the source's separate construction theorem in Lean.
