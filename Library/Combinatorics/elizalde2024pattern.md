---
bibkey: elizalde2024pattern
authors: Sergi Elizalde, Amya Luo
year: 2024
title: "Pattern avoidance in nonnesting permutations"
doi: 10.48550/arXiv.2412.00336
url: https://arxiv.org/abs/2412.00336v6
claim: "In Table 4 we list some cases that seem to give interesting enumeration sequences. All the conjectures have been checked for n up to 8."
strata_touched:
  - D5/S3/Combinatorics/Nonnesting/NonnestingFour
  - D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo
license: citation-only
triage: anchor
---

# Elizalde and Luo, pattern avoidance in nonnesting permutations

The paper enumerates nonnesting permutations of the multiset `{1,1,2,2,…,n,n}` avoiding every set of
at least two patterns of length three and several sets of patterns of length four, and closes with a
table of conjectured enumerations for further sets of patterns of length four.

## Verified locator

DOI: 10.48550/arXiv.2412.00336

URL: https://arxiv.org/abs/2412.00336v6

- Locator: Section 1, a word contains a pattern when some subsequence is in the same relative order,
  equal letters included; nonnesting permutations are the permutations of `{1,1,…,n,n}` avoiding `1221`
  and `2112`, and `c_n(Λ)` counts those avoiding every pattern of `Λ`.
- Locator: Section 4, Further research, Table 4: `{1322}` with `(1/n) Σ_{k=0}^{n-1} C(3n,k) C(2n-k-2,n-1)`
  (A007297); `{1132,2213}` and `{1233,1322}` with ordinary generating function
  `((1-x)^2 - √((1-x)^4 - 4x(1-x)^2))/(2x)` (A006319); `{1132,3312}` with `3^n - 3·2^{n-1} + 1`
  (A168583); `{1231,1312,2231,3221}` with ordinary generating function `(1-3x+2x^2)/((1-3x)(1-x-x^2))`
  (A099159).

## Reading of the statement

For `Λ = {1231,1312,2231,3221}` the conjectured counts for `n = 0, 1, …, 9` are
`1, 1, 4, 11, 33, 98, 293, 877, 2628, 7879`, the coefficients of the displayed rational function.

## Bounded prior-resolution evidence

Read on 2026-09-30: the Semantic Scholar citation list of arXiv:2412.00336 contains arXiv:2502.13309
(Archer and Laudone, one pattern of length three in noncrossing and nonnesting permutations),
arXiv:2608.21680 (Cowan, nonnesting permutations avoiding 123), arXiv:2608.21351 (Laudone, canon
permutations), arXiv:2608.30002 (Shankar, canon permutations) and arXiv:2312.16052; none treats the
Table 4 rows except that Demonstrandum Research published in July 2026 a Lean proof of the row
`{1132,3312}`. This is a bounded negative finding for the other rows.
