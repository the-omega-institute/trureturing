---
slug: elizalde-luo-nonnesting-1231-1312-2231-3221
bibkey: elizalde2024pattern
doi: 10.48550/arXiv.2412.00336
url: https://arxiv.org/abs/2412.00336v6
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Nonnesting/NonnestingFour.result
---

# Nonnesting Permutations Avoiding 1231, 1312, 2231 and 3221

## Problem

Sergi Elizalde and Amya Luo, *Pattern avoidance in nonnesting permutations*, arXiv:2412.00336v6,
Section 4, Table 4, row `{1231, 1312, 2231, 3221}`: the conjectured ordinary generating function of
`c_n({1231, 1312, 2231, 3221})` is `(1 - 3x + 2x^2)/((1 - 3x)(1 - x - x^2))`, with the remark

> All the conjectures have been checked for n up to 8.

Here a nonnesting permutation of size `n` is a permutation of `{1, 1, 2, 2, …, n, n}` avoiding `1221` and
`2112`, and pattern containment keeps equal letters equal.

## Motivation

The theorem `D5/S3/Combinatorics/Nonnesting/NonnestingFour.result` establishes the identity of formal
power series `C(x)(1 - 3x)(1 - x - x^2) = 1 - 3x + 2x^2` for `C(x) = Σ c_n x^n`, so
`c_n = 1, 1, 4, 11, 33, 98, 293, 877, 2628, 7879, …` and `c_n = 4c_{n-1} - 2c_{n-2} - 3c_{n-3}` for `n ≥ 3`.

## Gap

Pre-registration issue 11301 records the literature screen: none of the papers citing
arXiv:2412.00336 treats this row, and the repository had no result for it. This is a bounded negative
finding.

## Route

1. A doubled word avoids `1221` and `2112` exactly when its first and second occurrences appear in the
   same letter order.
2. Every word of the class splits uniquely at its value cuts into cut-free words, and direct sums of
   words of the class stay in the class; so `C = 1/(1 - D)` for the generating function `D` of cut-free
   words.
3. The four patterns force the first-occurrence order into consecutive blocks `k, 1, 2, …, k - 1`; a
   cut-free word of size `n ≥ 2` is either `n n v` with `v` of increasing first order, or one of two
   chains, so there are `2^{n-2} + 2` of them, and `D = x + x^2/(1 - 2x) + 2x^2/(1 - x)`.

## Falsifier

The statement would fail if some `n` had a count different from the coefficient of the rational function.
It depends on reading containment with equal letters kept equal.

## Evidence

Exhaustive enumeration through `n = 11` agrees with every structural lemma and with the counts, including
`c_{10} = 23629` and `c_{11} = 70874`.

## Triage

`theorem`; the conjecture is stated in Table 4 of arXiv:2412.00336 and is quantified over every `n`.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, arXiv searches and repository checks recorded
above.
