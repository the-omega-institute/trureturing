---
bibkey: lee2026multivariateindependence
authors: Joonkyung Lee; Jaehyeon Seo
year: 2026
title: "Lower bounds for multivariate independence polynomials and their generalisations"
doi: 10.48550/arXiv.2602.02450
url: https://arxiv.org/abs/2602.02450v2
claim: "Section 5 proposes the occupancy-fraction strengthening (5.2), equivalent to sum_v p_v(lambda) >= sum_v lambda_v/(1+(d_v+1)lambda_v) for all nonnegative vertex fugacities."
strata_touched:
  - D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation
license: citation-only
triage: anchor
---

# Lee and Seo, multivariate independence polynomials

Section 5, page 16, under "Occupancy fractions", states:

> Having seen the Davies–Kang conjecture, it seems plausible to look for a strengthening of Theorem 1.1 in terms of occupancy fractions.

The vertex occupancy `p_v(λ) := λ_v ∂/∂λ_v log Z_G(λ)` is the probability
that `v` belongs to a hard-core independent set. The paper defines
`α_G(t; λ) = (1/|V(G)|) Σ_{v∈V(G)} p_v(tλ)` and proposes

$$
\alpha_G(t;\lambda)\ge\frac{1}{|V(G)|}
\sum_{v\in V(G)}\alpha_{K_{d_v+1}}(t\lambda_v),\qquad
t\in\mathbb R_{\ge0},\quad\lambda\in(\mathbb R_{\ge0})^{V(G)}.
\tag{5.2}
$$

Here `α_{K_{d+1}}(x) = x/(1+(d+1)x)` by (5.1). The subsequent sentence reads:

> Moreover, (5.2) is equivalent to showing that for all λ ∈ (R_{≥0})^{V(G)},

$$
\sum_{v\in V(G)}p_v(\lambda)\ge
\sum_{v\in V(G)}\alpha_{K_{d_v+1}}(\lambda_v).
$$

The proposed statement fails already at `t = 1` on `K_{1,2}` with
fugacities `(15,2,2)`: the sum of occupancies is `9/8`, smaller than
`15/46 + 2/5 + 2/5 = 259/230`. All entries are strictly positive.
This disproves the proposed strengthening, and does not contradict the
partition-function lower bound of Theorem 1.1: integrating a proposed
stronger pointwise bound is a sufficient route to that theorem.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2602.02450
- URL: https://arxiv.org/abs/2602.02450v2
- Version 2, Section 5, page 16, "Occupancy fractions", equations (5.1),
  (5.2), and the equivalent vertex-marginal inequality.
