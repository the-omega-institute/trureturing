---
slug: elizalde-luo-nonnesting-1322
bibkey: elizalde2024pattern
doi: 10.48550/arXiv.2412.00336
url: https://arxiv.org/abs/2412.00336v6
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result
---

# Nonnesting Permutations Avoiding 1322

## Problem

Sergi Elizalde and Amya Luo, *Pattern avoidance in nonnesting permutations*, arXiv:2412.00336v6,
Section 4, Table 4, row `{1322}`: the conjectured number of nonnesting permutations of
`{1, 1, 2, 2, …, n, n}` avoiding `1322` is `(1/n) Σ_{k=0}^{n-1} C(3n, k) C(2n-k-2, n-1)` (OEIS A007297),
with the remark

> All the conjectures have been checked for n up to 8.

## Motivation

The theorem `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.result` establishes
`n · c_n({1322}) = Σ_{k<n} C(3n, k) C(2n-k-2, n-1)` for every `n ≥ 1`, so the counts are
`1, 4, 23, 156, 1162, 9192, 75819, …`, the numbers of connected graphs on `n + 1` labelled points on a
circle with noncrossing edges.

## Gap

Pre-registration issue 11302 records the literature screen: none of the papers citing
arXiv:2412.00336 treats this row, and the repository had no result for it. This is a bounded negative
finding.

## Route

1. A nonnesting word is a permutation (its first-occurrence order) together with a Dyck word, and it
   contains `1322` exactly when some letters `a < c < b` occur as `a`, then `b`, before the first copy of
   `c`; hence the first-occurrence order avoids `132` and splits as `B A z` at its last entry `z`.
2. Every word of the class is obtained, uniquely, by one of two insertions of `z` into a pair of smaller
   words of the class, recorded with the length of the terminal run of second copies.
3. The resulting catalytic equation for the bivariate generating function, solved by the kernel method,
   gives `G = x(1 + G)^3/(1 - G)` for `G = Σ_{n≥1} c_n x^n`, and the coefficients of this equation are the
   displayed binomial sums.

## Falsifier

The statement would fail if some `n ≥ 1` had a count different from the displayed sum. It depends on
reading containment with equal letters kept equal.

## Evidence

Exhaustive enumeration through `n = 9` agrees with every structural lemma and with the counts, including
`c_8 = 644908` and `c_9 = 5616182`.

## Triage

`theorem`; the conjecture is stated in Table 4 of arXiv:2412.00336 and is quantified over every `n`.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, arXiv searches and repository checks recorded
above.
