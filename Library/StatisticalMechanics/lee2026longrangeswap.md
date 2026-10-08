---
bibkey: lee2026longrangeswap
authors: Eunghyun Lee
year: 2026
title: Integrability of multispecies long-range swap models with species-dependent interpolation
doi: 10.1088/1742-5468/ae80b5
url: https://arxiv.org/abs/2604.12136v1
claim: "Remark 3.1 conjectures that every reduction operator 𝔄_k is invertible for every species-dependent parameter μ_i in [0,1]."
strata_touched:
  - D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit
  - D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1742-5468/ae80b5

Source: https://arxiv.org/abs/2604.12136v1

Crossref identifies the author, title, DOI, and publication in Journal of
Statistical Mechanics: Theory and Experiment, 2026, 073102.
Equation (7), source label `138am42`, page 10, defines the local matrices B and B′.
Lemma 3.4, equation (26), page 17, gives the adjacent coefficients
ℬ_i and ℬ′_i. Equation (28), source label `1122am331`, defines
𝔄_0 = I and 𝔄_k = I − ℬ_{k+1} 𝔄_{k−1}^{−1} ℬ′_k.
Remark 3.1 immediately after it, page 18, states:

> These results lead us to conjecture that 𝔄_k is invertible for all parameters μ_i ∈ [0,1].

Section 2.3, page 7, states:

> The invertibility of the general case (μ_i ∈ (0,1) with arbitrary species composition) remains open due to the complexity of the operators arising in the reduction procedure.

The public encoding uses species `Fin N`, words `Fin n → Fin N`, and real
matrices indexed by words. For N ≥ 1, n ≥ 2, j ≥ 1, and j + k + 1 ≤ n,
`claim` requires `IsUnit (A μ j k)` for every parameter vector with
0 ≤ μ a ≤ 1. The adjacent-slot entry rule is the paper's tensor product
in word coordinates, with zero-based slot j + i − 2 corresponding to the
paper's one-based slot j + i − 1.

Proposition 2.2, “Integrability under invertibility”, and the Yang–Baxter
result explain the consequence for the source's reduction to two-particle
interactions. The spectral-radius observation in Remark 3.1 is a separate
numerical statement and is not an assumption of the invertibility proof.
