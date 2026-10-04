---
bibkey: lumbroso2013ddg
authors: Jeremie Lumbroso
year: 2013
title: "Optimal Discrete Uniform Generation from Coin Flips, and Applications"
doi: null
url: https://arxiv.org/abs/1304.1916v1
claim: "Section 2.1, equations (1)-(3), gives the optimal DDG random-bit cost as a sum of dyadic fractional parts."
strata_touched:
  - D5/S3/Arith/FibonacciAtomic/FiveOutcomeDyadicSupportBound
license: citation-only
triage: anchor
---

# Dyadic fractional-part cost

Section 2.1, equations (1)-(3), recalls the Knuth-Yao optimal DDG cost
as the sum over outcomes and nonnegative depths of
the fractional part of the depth-scaled probability divided by that scale.
For a probability vector whose coordinates sum to one, this is exactly
the series of the integer residuals
`2^d - sum_i floor(2^d p_i)` divided by `2^d`.

This supplies the classical cost expression. It does not state the
five-outcome supporting inequalities in terms of the smallest coordinate.

## Verified locator

https://arxiv.org/abs/1304.1916v1

https://arxiv.org/pdf/1304.1916v1, Section 2.1, equations (1)-(3).
