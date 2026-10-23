---
bibkey: sun2021weighteddistinctsums
authors: Zhi-Wei Sun
year: 2021
title: "On permutations of {1,...,n} and related topics"
doi: 10.1007/s10801-021-01028-8
url: https://arxiv.org/abs/1811.10503v6
claim: "Conjecture 4.9 gives a lower bound for weighted sums of distinct elements of a finite subset of a field."
strata_touched:
  - D5/S3/Arith/Additive/SunWeightedDistinctSums
license: citation-only
triage: anchor
---

# Sun's weighted distinct-sum conjecture

Zhi-Wei Sun, *On permutations of {1,...,n} and related topics*,
*Journal of Algebraic Combinatorics* 54 (2021), 893–912,
DOI [10.1007/s10801-021-01028-8](https://doi.org/10.1007/s10801-021-01028-8),
arXiv:1811.10503v6.

Conjecture 4.9, page 18, states:

> Conjecture 4.9. Let n ∈ Z+ and let F be a field with p(F) > n + 1, where p(F) = p if the characteristic of F is a prime p, and p(F) = +∞ if the characteristic of F is zero. Let A be any finite subset of F with |A| ⩾ n + δ_{n,3}, where δ_{n,3} is 1 or 0 according as n = 3 or not. Then, for the set S(A) := {Σ_{k=1}^n k a_k : a_1, . . . , a_n are distinct elements of A} (4.8), we have |S(A)| ⩾ min{p(F), (|A| − n) n(n+1)/2 + n(n²−1)/6 + 1}. (4.9)

The repository module `D5/S3/Arith/Additive/SunWeightedDistinctSums` checks the negation of this conjecture. At n = 2 and A = {0,1,2} in ℚ, the six ordered pairs produce {1,2,4,5}, so the cardinality is 4 while the bound is 5.

Remark 4.9, on the same page, compares Conjecture 4.9 with the conjectural linear extension of the Erdős–Heilbronn conjecture and proposes replacing the field by a finite additive group, with the least prime factor of its order in place of $p(F)$. The additive groups of the tested prime fields inherit the same counterexample.

## Verified locator

DOI: https://doi.org/10.1007/s10801-021-01028-8

Source: https://arxiv.org/abs/1811.10503v6
