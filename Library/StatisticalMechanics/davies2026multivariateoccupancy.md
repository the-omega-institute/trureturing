---
bibkey: davies2026multivariateoccupancy
authors: Ewan Davies; Juspreet Singh Sandhu; Jaehyeon Seo; Brian Tan
year: 2026
title: "Degree-sequence bounds for independent sets via multivariate local occupancy"
doi: 10.48550/arXiv.2605.05149
url: https://arxiv.org/abs/2605.05149v1
claim: "Section 1 proposes that the degree-sequence hard-core occupancy bound E|I| >= sum_v lambda_v/(1+(d_v+1)lambda_v) holds on the positive orthant without the small-fugacity restriction of Theorem 1."
strata_touched:
  - D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation
license: citation-only
triage: anchor
---

# Davies, Sandhu, Seo and Tan, multivariate local occupancy

Section 1, page 1, defines the hard-core measure:

> For a fugacity vector λ ∈ [0, ∞)^V we define for any I ∈ I(G) the measure

$$
P_{G,\lambda}(I)=\frac{1}{Z_G(\lambda)}\prod_{v\in I}\lambda_v,
$$

> where Z_G(λ) = Σ_{J∈I(G)} ∏_{v∈J} λ_v is the normalizing constant known as the partition function that makes this a probability measure.

Expectation of cardinality under this measure is
`Σ_{I∈I(G)} |I| ∏_{v∈I} λ_v / Z_G(λ)`. Theorem 1, page 2,
proves the degree-sequence lower bound
`E_{G,λ}|I| ≥ Σ_{u∈V(G)} λ_u/(1+(d_u+1)λ_u)` under
`λ_u < 1/Δ` for every vertex, where `Δ` is the maximum degree.
The paragraph after the theorem states:

> Strengthening the conjecture, we believe that the multivariate version should hold for any λ in the positive orthant.

> The bound in Theorem 1 is tight by the example of a disjoint union of complete graphs (such that λ is constant on each component), though we believe that the upper bound on the entries of λ can be removed.

The positive-orthant extension fails on the star `K_{1,2}` with center
fugacity 15 and leaf fugacities 2,2. Its independent-set partition is 24,
its weighted cardinality sum is 27, and `27/24 = 9/8 < 259/230`, the proposed
lower bound. The example lies outside the restricted range of Theorem 1
and uses unequal fugacities; it does not refute the univariate Davies–Kang
Conjecture A referred to in the same paragraph.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2605.05149
- URL: https://arxiv.org/abs/2605.05149v1
- Version 1, Section 1, page 1 (measure and partition), page 2 (Theorem 1
  and the positive-orthant extension).
