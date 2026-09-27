---
bibkey: reyesbustos2026twophotonrabi
authors: Cid Reyes-Bustos, Masato Wakayama
year: 2026
title: "Two-photon quantum Rabi models – Spectral degeneracy and symmetries"
doi: 10.48550/arXiv.2609.00750
url: https://arxiv.org/abs/2609.00750v1
claim: "The paper studies the spectrum of the two-photon asymmetric quantum Rabi model, proves divisibility relations between constraint polynomials for shared-parity degeneracies, and conjectures that the constraint polynomial at the critical coupling x = 1 factors as a product of linear factors y + 2n(2n + 2rho - 1) and that for x > 1 it has positive coefficients."
strata_touched:
  - D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials
license: citation-only
triage: anchor
---

# Two-photon quantum Rabi models – Spectral degeneracy and symmetries

Reyes-Bustos and Wakayama study the two-photon asymmetric quantum Rabi model
with coupling `g`, level splitting `2Δ` and bias `ε ∈ ℝ`, with parity
`ρ ∈ {0, 1}`. Juddian (polynomial) eigenfunctions exist exactly when a
constraint polynomial vanishes. Definition 4.1 gives these polynomials in
`x = (2g)^2` and `y = Δ^2` by the three-term recursion

> P_0 = 1, P_1 = y + 2x(4N + 2ρ + 2ε − 1) − 4(1 + ε),
> P_k = (y + 2xk(4N + 2ρ − 2k + 2ε + 1) − 4k(k + ε)) P_{k−1}
>   − 4k(k − 1)(2(N − k + 1) + ρ)(2(N − k + 1) + ρ − 1) x P_{k−2},

and calls `P_N^{(N,ρ,±ε)}` the constraint polynomial. Proposition 4.4 records
that `P_N^{(N,ρ,±ε)}(1, y)` does not depend on `ε`. After leaving "a complete
description of this as an open problem", the paper states Conjecture 4.5:

> We have P_N^{(N,ρ,ε)}(1, y) = ∏_{n=1}^{N} (y + 2n(2n + 2ρ − 1)). Moreover,
> for x > 1, the polynomial P_N^{(N,ρ,ε)}(x, y) has positive coefficients,
> and therefore, no positive roots for y.

The critical value `x = 1` corresponds to `g = 1/2`, where the model acquires
continuous spectrum. In the paper's own examples at `x = 1`, the product
printed for `P_5^{(5,1,ε)}` carries the roots of the case `ρ = 0`.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2609.00750
- URL: https://arxiv.org/abs/2609.00750v1
- Version and location: arXiv:2609.00750v1 (2026-09-01, the only version), source file `main.tex`: §2 for the bias `ε ∈ ℝ`; §4 for Definition 4.1 (`dfn:copo`), Proposition 4.4 and Conjecture 4.5 (the `conject` environment numbered with the theorem counter within §4).
