---
bibkey: novaes2023absorption
authors: M. Novaes
year: 2023
title: "Time delay statistics for chaotic cavities with absorption"
doi: 10.1007/s10955-023-03183-7
url: https://arxiv.org/abs/2305.18235v1
claim: "Section 5: Eqs. (54) and (55), strong-absorption moment expansions for every positive channel count and order; Eq. (58), the first two cumulant coefficients for every M ≥ 1 and n > 1."
strata_touched:
  - D5/S3/Quantum/Transport/StrongAbsorption/Foundations
  - D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments
  - D5/S3/Quantum/Transport/StrongAbsorption/Density
  - D5/S3/Quantum/Transport/StrongAbsorptionCumulants
  - D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity
  - D5/S3/Quantum/Transport/StrongAbsorptionMoments
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/s10955-023-03183-7

Source: https://arxiv.org/abs/2305.18235v1

M. Novaes, *Journal of Statistical Physics* 190, 182 (2023).
The following page numbers and equation numbers refer to arXiv v1.

## Model and conjecture

Section 1, Eqs. (2)–(3), uses dwell-time units and defines
$Q(\gamma)=(1_M-SS^\dagger)/\gamma$ and $\gamma=\tau_d/\tau_a$.
The source says: “τW = (1/M) Tr(Q) is called the Wigner time delay”.

Section 5, p. 7:

> we conjecture that, for n > 1,

$$
(-1)^n k_n(\gamma)
=\frac{(n-1)!}{M^{2n-2}\gamma^{2n}}
-\frac{(2n-1)n(n-1)!}{M^{2n-2}\gamma^{2n+1}}
+O(\gamma^{-2n-2}). \tag{58}
$$

The channel number is any positive integer. The cumulant order is any
integer at least two. The constants in the remainder may depend on both.
The author-hosted journal text numbers the same conjecture Eq. (65).

The joint law is supplied by A. Grabsch, *Distribution of the Wigner–Smith
time-delay matrix for chaotic cavities with absorption and coupled Coulomb
gases*, *Journal of Physics A* 53, 025202 (2020),
DOI: 10.1088/1751-8121/ab5c87,
https://arxiv.org/abs/1909.01002v2, Eqs. (3)–(4).
At β = 2 and N = M, write the inverse delay rates as Γᵢ = γ + xᵢ.
The weight on xᵢ ≥ 0 and 0 ≤ yⱼ ≤ γ is
$e^{-M(\sum x_i+\sum y_j)}\Delta(x)^2\Delta(y)^2
\prod_{i,j}(\gamma+x_i-y_j)$.
Its total mass normalizes the measure, and
$\tau_W=M^{-1}\sum_i(\gamma+x_i)^{-1}$.

The formal cumulant is the n-th derivative at zero of the cumulant
generating function of this observable under this normalized measure.
The conclusion gives an explicit eventual absolute bound with denominator
$\gamma^{2n+2}$. It determines two coefficients; the next coefficient,
uniform bounds in M, and the β = 1, 4 classes remain open here.

## Strong-absorption moments

Section 5, arXiv v1, p. 7:

> We conjecture that (1/M)⟨Tr(Qⁿ)⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n²/γⁿ⁺² − (n + 1)[n(5n − 2)M² + n(n + 2)]/(6M²γⁿ⁺³) + O(γ^{−n−4}) (54) and that (1/Mⁿ)⟨[Tr(Q)]ⁿ⟩ is given by 1/γⁿ − n/γⁿ⁺¹ + n[(n + 1)M² + (n − 1)]/(2M²γⁿ⁺²) + O(γ^{−n−3}), (55) for every positive integer n.

The proper delay times are qᵢ = 1/(γ + xᵢ). The normalized spectral
observable is M⁻¹ Σᵢ qᵢⁿ, and the Wigner observable is
(M⁻¹ Σᵢ qᵢ)ⁿ. The eventual absolute remainder constants may depend
on both M and n. Uniformity in either parameter and higher asymptotic
orders are open here.
