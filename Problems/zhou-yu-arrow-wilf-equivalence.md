---
slug: zhou-yu-arrow-wilf-equivalence
bibkey: zhou2026arrow
doi: 10.48550/arXiv.2609.29392
url: https://arxiv.org/abs/2609.29392v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ArrowWilfEquivalence.result
---

# The Arrow Patterns (12; 3 → 3) and (23; 1 → 1) Are Arrow-Wilf-Equivalent

## Problem

Robin D.P. Zhou and Xinyang Yu, *Arrow-Wilf equivalences and enumerative results for short arrow
patterns*, arXiv:2609.29392v1, Section 7:

> We have computed the avoidance counts for the arrow patterns (12; 3 → 3) and (23; 1 → 1) and found that
> the resulting sequences agree for all values of n tested. This suggests that these two patterns may be
> arrow-Wilf-equivalent. However, the explicit formulas we obtained for the two sequences are quite
> different in form, and we have not been able to establish the equivalence by a direct bijection or by
> any other method. We leave this as an open problem.

Arrow-Wilf equivalence means `|S_n(12; 3 → 3)| = |S_n(23; 1 → 1)|` for every `n ≥ 1`, with containment of
an arrow pattern as defined in Section 1 of the paper through `π̂ = θ⁻¹(π)`.

## Motivation

The frozen theorem `D5/S3/Combinatorics/ArrowWilfEquivalence.result` proves the equivalence for every
`n ≥ 1`. It is the equinumerosity the authors observed numerically and could not prove, and it relates
a class described through the largest fixed point of `π̂` to a class described through the smallest one.

## Gap

Issue 9847 records the screen made before the work. The arXiv record has only v1; searches by title,
arXiv number and the two pattern names found no later proof; google-deepmind/formal-conjectures and
conjectures.io have no entry. Nothing under `Problems/`, `D5/` or `Library/`, and no entry of the three
screening records, concerns this paper.

## Route

1. `f` is a fixed point of `π̂` exactly when `f` is a left-to-right maximum of `π` followed by a larger
   entry or by the end. Hence `π` avoids `(12; 3 → 3)` iff the entries below every fixed point appear in
   decreasing order, and avoids `(23; 1 → 1)` iff the entries above every fixed point appear in
   decreasing order.
2. Decomposing by the largest fixed point gives the count of Theorem 3.1, and decomposing by the smallest
   fixed point gives the count of Theorem 5.5; both decompositions are explicit bijections with decorated
   objects built from a derangement, a subset and a weak composition.
3. With `E_n = Σ_{p=0}^{n−1} Σ_{i=0}^{p} (−1)^i (p!/i!) C(n−i−1, p−i)`, the first correction term equals
   `E_n` after the reindexing `n − m = k + r`, `m = h + r + 1`, which turns the binomial product into a
   trinomial coefficient, and the finite negative-binomial expansion of `(1 − z − z²)^{−(k+1)}`. The second
   correction term equals `E_n` after the substitution `k = m − 1 − r`, the inclusion–exclusion formula for
   `d_k` and a hockey-stick summation; its boundary term `d_{n−1}` is the term `p = n − 1` of `E_n`.
4. Both counts equal `d_n + E_n`.

## Falsifier

The statement would fail if some `n` had different avoidance counts. It would fail to be the paper's
statement if `π̂` were read with cycles cut at left-to-right minima, or if containment ignored the order of
the selected values; the formal definitions follow Section 1 literally and agree with an independent
brute-force implementation on every permutation with `n ≤ 7`.

## Evidence

Brute-force enumeration from the Section 1 definitions gives 1, 2, 5, 17, 75, 412, 2707, 20657 for both
classes at `n = 1, …, 8`, matching both formulas. The two formulas and `d_n + E_n` agree for every
`1 ≤ n < 120`, and every intermediate identity of the route was checked for `n ≤ 60`.

## Triage

`theorem`; Tier 1 open problem stated at the end of a 2026 paper, preregistered in issue 9847 before the
work. The computational use is `none`: the delivered statement is universally quantified over every
`n ≥ 1`, and no declaration is a bounded enumeration, a checker, a numeric reduction or a certified
instance.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above; the paper was one day old when screened,
so no worldwide priority claim is made. No direct bijection between the two classes is given; the
equivalence passes through the common signed sum.
