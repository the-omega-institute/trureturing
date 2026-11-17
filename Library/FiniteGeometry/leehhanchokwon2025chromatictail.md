---
bibkey: leehhanchokwon2025chromatictail
authors: W. Lee; M. Hhan; G. Y. Cho; H. Kwon
year: 2025
title: Shallow quantum circuit for generating extremely low-entangled approximate state designs
doi: 10.48550/arXiv.2507.17871
url: https://arxiv.org/abs/2507.17871v3
claim: Supplemental Material §4 conjectures an O(t log t) chromatic-index bound with failure probability smaller than epsilon in the stated low-failure regime.
strata_touched:
  - D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2507.17871

Source: https://arxiv.org/abs/2507.17871v3

## Source statement

Supplemental Material §4, p. 17:

> Additionally, let us set k = 3 log(t²/ϵ), m = log t, and α = βt log(1/ϵ).

> Then, the chromatic index χ′(H) of H is exactly the minimum depth of applying all the gates.

> Each edge of H contains v with the probability of m/k. Since each edge is sampled independently

Page 18, after Eq. (87):

> One may see that if log(1/ϵ) scales with t^{1+c} for some c > 0, and β is set by β > 1 + c, then these two conditions are simultaneously satisfied.

> We conjecture that in this regime, χ′(H) is upper bounded by O(t log t) with a failure probability smaller than ϵ.

## Mathematical scope

The finite model uses alpha independent uniformly sampled m-element subsets of
Fin k, with occurrence indices in Fin alpha. Repeated subsets remain distinct
edge occurrences. The chromatic index is the least natural colour count making
distinct intersecting occurrences differently coloured. Logarithms are base two;
k, m and alpha are rounded up with natural ceilings. The chosen regime member
is eps(c,t) = 2^(−t^(1+c)).

The repository refutation uses c = 1, beta = 3 and a doubly dyadic sequence of t.
A fixed nonempty edge repeated in a sufficiently long prefix gives a probability
lower bound 1/k^(m*r), which already exceeds eps. This proves neither the sharper
binomial lower bound (m/k)^r nor the variant with pairwise distinct edges.
Eq. (87)'s weaker failure probability O(1/log t) is outside the refutation.

The exact-enumeration experiment is in
`the-omega-institute/trureturing-experiments`, commit `101c5f2b`,
`docs/reports/lee-hhan-cho-kwon-2025-chromatic-index-tail/check.py`,
SHA-256 `5800bc5cdf3838f94680993ccb2aacbb776d11ef7c3e8e1a8b47b0318ef9e6f1`.
The recorded checker exit code is 0. Its output has SHA-256
`3e4bb90fb698f7eff650d7178614e73e9156fd4de490957cc24f81dad0d9ad2c`.

Literature completeness and the status of the final journal supplement remain
ASSUMED-UNVERIFIED. The cited source is arXiv version three.
