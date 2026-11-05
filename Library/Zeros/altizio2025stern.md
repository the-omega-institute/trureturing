---
bibkey: altizio2025stern
authors: David Altizio
year: 2025
title: Zeros of Stern polynomials in the complex plane
doi: 10.48550/arXiv.2511.03847
url: https://arxiv.org/abs/2511.03847v1
claim: Remark 4 asks whether the bound |(z)_n| ≥ n|z| on |z − 2| ≤ 1 holds exactly for n = 5, 6, 7.
strata_touched:
  - D5/S3/Zeros/AltizioGeometricSumDisk
license: citation-only
triage: anchor
---

# Geometric sums on the Stern exclusion disk

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2511.03847

Source: https://arxiv.org/abs/2511.03847v1

## Source statement

Section 2, p. 4: “For all positive integers n, we introduce the
(non-standard) notation (λ)_n := 1 + λ + ⋯ + λ^{n−1} =
(λ^n − 1)/(λ − 1) ∈ ℤ[λ].” The source sets (1)_n = n by continuity.

Section 3: “B := B_1[2] = {|w − 2| ≤ 1}”.

Section 4.3, p. 20, Remark 4: “One might suspect that |(z)_n| ≥ n|z|
more generally whenever z ∈ B. However, numerical evidence suggests that
the value min_{z∈B} |(z)_n/z| approaches 2π as n → ∞. It seems that this
inequality is true only for n = 5, 6, and 7, but we do not have a proof.”

## Mathematical scope

The finite sum is `∑ k ∈ Finset.range n, z ^ k` for positive natural n.
The disk is `Metric.closedBall (2 : ℂ) 1`. The classification quantifies
over every point of this closed disk and both directions of the degree
criterion. Proposition 8 supplies the source's degree-five and degree-six
bounds. The repository result proves the classification, including degree
seven and the excluded positive degrees. The 2π limit and the separate
inequality in Remark 3 are outside that result.

## Supporting computation and literature boundary

The exact-arithmetic experiment is in
`the-omega-institute/trureturing-experiments`, commit
`65ee1fc450d3e106194a87a31f910d2ef1ba35bd`, at
`docs/reports/altizio-2025-geometric-sum-disk/check.py`, SHA-256
`cc441905676ba7ed3924ce669b140bf6869da609f92bfcfe8b162a57cd26181d`.
It exits 0 and checks the three polynomial certificates, the source's
Proposition 8 identities, and the excluded-degree coefficient and rational
parameters through degree 60. These finite checks do not prove the
unbounded classification.

The literature screen on issue
[#20656](https://github.com/the-omega-institute/trureturing/issues/20656)
includes the arXiv version and the author's dissertation. Its completeness
is `ASSUMED-UNVERIFIED`; the source is cited as posing the question, not as
proving its answer.
