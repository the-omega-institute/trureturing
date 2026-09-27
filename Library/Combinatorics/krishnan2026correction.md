---
bibkey: krishnan2026correction
authors: Arnav Krishnan
year: 2026
title: "A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)"
doi: 10.48550/arXiv.2607.19412
url: https://arxiv.org/abs/2607.19412v1
claim: "Conjecture 5. Z(P(n,3)) = 8 for every n ≥ 13."
strata_touched:
  - D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree
license: citation-only
triage: anchor
---

# Krishnan, the zero forcing number of P(n,3)

The note corrects a published claim that `Z(P(n,3)) = 8` for all `n ≥ 12`: it exhibits a 7-vertex zero forcing set of `P(12,3)`, proves the
upper bound `Z(P(n,3)) ≤ 8` for `n ≥ 9`, computes `Z(P(n,3))` for `7 ≤ n ≤ 20` by exhaustive search, and states the corrected lower bound as
a conjecture.

## Verified locator

DOI: 10.48550/arXiv.2607.19412

URL: https://arxiv.org/abs/2607.19412v1

The arXiv record shows only v1 (13 July 2026).

- Locator: Proposition 4, "For every n ≥ 9, S = {u_0, …, u_7} is a zero forcing set of P(n,3)."
- Locator: Table 1, `Z(P(n,3))` for `7 ≤ n ≤ 20`, equal to 8 for `13 ≤ n ≤ 20` and to 7 for `n = 11, 12`.
- Locator: Conjecture 5, "Z(P(n,3)) = 8 for every n ≥ 13." The following paragraph reads: "the content is the lower bound Z(P(n,3)) ≥ 8
  for all n ≥ 13, which we verified only for n ≤ 20. Proving it for all n means excluding 7-vertex forcing sets uniformly in n".
- Locator: Section 5, "Whether they stay 8 for all larger n (Conjecture 5) is open".

## Reading of the statement

`P(n,3)` has outer vertices `u_i`, inner vertices `v_i` (indices mod `n`), outer-cycle edges `u_i u_{i+1}`, spokes `u_i v_i` and inner edges
`v_i v_{i+3}`. A set `S` is zero forcing when repeatedly letting a black vertex with exactly one white neighbour colour that neighbour black
turns every vertex black; `Z` is the least size of such a set. Conjecture 5 asserts `Z(P(n,3)) = 8` for every `n ≥ 13`.

## Scope of the recorded answer

The conjecture holds. The upper bound is Proposition 4. For the lower bound, if a zero forcing set performs at least `p` forces then the
set `X` of its first `p` forcing vertices satisfies `|N(X)| ≤ |S|`, where `N(X)` is the external vertex boundary; for `n ≥ 14` every 10-vertex
set of `P(n,3)` has `|N(X)| ≥ 8`, which excludes 7-vertex forcing sets, and `n = 13` is settled by explicit forts meeting every 7-vertex
candidate.

## Bounded prior-resolution evidence

Read on 2026-09-24 and 2026-09-26: the arXiv record (v1 only); google-deepmind/formal-conjectures, conjectures.io and mathdb by title,
arXiv number and the terms "zero forcing" and "Petersen" returned no match. This is a bounded negative finding.
