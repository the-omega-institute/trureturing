---
slug: archer-bourne-square-tetranacci-refutation
bibkey: archer2026pattern
doi: 10.46298/dmtcs.17199
url: https://arxiv.org/abs/2505.05218v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result
---

# The Archer–Bourne Square Recurrence Fails at n = 11

## Problem

Kassie Archer and Noel Bourne, *Pattern avoidance in compositions and powers of permutations*, arXiv:2505.05218v3,
Section 5, printed page 14:

> For example, we conjecture that if we take a_n := a_n(312, 54321 : 132) then a_n = a_{n−1} + a_{n−2} + a_{n−3} +
> a_{n−4} + n − 1 for n ≥ 6.

Here a_n(312, 54321 : 132) is the number of permutations π of [n] that avoid 312 and 54321 and whose square π ∘ π
avoids 132.

## Motivation

The theorem `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result` proves that the stated
recurrence does not hold for every n ≥ 6.

## Gap

Pre-registration issue 12226 records the literature screen: no work citing arXiv:2505.05218 was located, and the
GitHub search for the identifier returned no hit outside this repository. This is a bounded negative finding.

## Route

1. A nonempty 312-avoider is ρ ⊕ τ with ρ its first direct-sum component. If π² avoids 132, then τ² is increasing,
   so τ is an involution; a 312-avoiding involution is a direct sum of decreasing blocks, of length at most four
   because of 54321.
2. Hence a_n = a_{n−1} + a_{n−2} + a_{n−3} + a_{n−4} + b_n for every n ≥ 5, where b_n counts the admissible
   indecomposable first components of length n.
3. The conjectured recurrence is therefore equivalent to b_n = n − 1 for every n ≥ 6. Every admissible component
   arises by inserting its maximum before a decreasing suffix of length at most three; a kernel-checked search over
   the 4181 candidates of length 11 finds exactly nine admissible components, so b_11 = 9.

## Falsifier

The refutation would fail if the decomposition missed a member or counted one twice, or if the candidate generator
missed an admissible component of length 11.

## Evidence

a_1, …, a_12 = 1, 2, 5, 11, 22, 45, 89, 174, 338, 655, 1265, 2442, computed independently by two exhaustive
programs. The recurrence holds for n = 6, …, 10 and fails at n = 11 (it predicts 1266) and n = 12 (it predicts
2443).

## Triage

`theorem`; the conjecture of Section 5 of arXiv:2505.05218v3 is refuted.

- Proved (formalized): a_n = a_{n−1} + a_{n−2} + a_{n−3} + a_{n−4} + b_n for every n ≥ 5, and b_11 = 9, so the
  recurrence fails at n = 11.
- Computed: b_5, …, b_12 = 3, 5, 6, 7, 8, 9, 9, 10. The conjecture holds exactly when b_n = n − 1, which is true
  for 6 ≤ n ≤ 10 and false for n = 11, 12. The data reflect the source's own boundary: the recurrence also fails
  for n = 4, 5.
- Open: a closed form for b_n, and hence for a_n. The structure above reduces it to classifying the admissible
  indecomposable components, whose first value is at most four; the source's broader question of enumerating
  a_n(312, k…21 : σ) for other k and σ is untouched.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation index, the arXiv and GitHub searches and the repository checks
recorded above.
