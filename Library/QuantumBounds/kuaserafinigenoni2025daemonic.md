---
bibkey: kuaserafinigenoni2025daemonic
authors: K. H. Kua; A. Serafini; M. G. Genoni
year: 2025
title: "Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection"
doi: 10.1088/2058-9565/ae2200
url: https://arxiv.org/abs/2506.22288
claim: "Section VI, Eq. (66), gives the aligned pure optimum and conjectures its optimality over all steady-state general-dyne monitoring."
strata_touched:
  - D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1088/2058-9565/ae2200

Source: https://arxiv.org/abs/2506.22288

The source is arXiv:2506.22288v2 and Quantum Sci. Technol. 11, 015014 (2026).

## Section VI and Eq. (66)

Page 12, verbatim text (the displayed equation is retained separately):

> As regards the optimization over all the generaldyne measurement, one proves that if one fixes the measurement phase to zero, ϑ_m = 0, then the conditional steady-state purity, and as a consequence the daemonic ergotropy is maximized for the general-dyne parameter

$$
z_{m,\mathrm{opt}} = \frac{1-\tilde\chi}{1+\tilde\chi}. \tag{66}
$$

> We have also numerically verified that non-zero phases ϑ_m lead to worse result, and we can thus conjecture that this fully characterizes the optimal steady-state general-dyne monitoring.

Here ν_in = 2n_th + 1, κ > 0 and 0 ≤ χ < κ/2; the dimensionless pump is r = 2χ/κ. The measurement covariance at zero phase is diag(z_m, 1/z_m). All finite symmetric real measurement covariances satisfying σ_m + iΩ ≥ 0, including mixed measurements with determinant at least one, enter the optimality question.

## Covariance equations

Equations (21)–(25) and (55) give Ãσ + σÃᵀ + D̃ − σBBᵀσ = 0, with Ã = A + EBᵀ, D̃ = D − EEᵀ, E = ΩCσ_in(σ_in + σ_m)⁻¹ᐟ² and B = CΩ(σ_in + σ_m)⁻¹ᐟ². Equations (57)–(58) give A = diag(−κ/2 − χ, −κ/2 + χ), D = κν_in I and σ_in = ν_in I. The physical q,p symplectic matrix is [[0, 1], [−1, 0]]; choosing C = √κ Ω gives these drift and diffusion matrices and the unrotated optimizer of Eq. (66).

## Scope of the optimality conclusion

The global lower bound and an aligned pure attainer are repository-derived. They apply to every physical stationary covariance solving the source equation. They do not classify every equality case; at zero pump or zero temperature, equality need not single out the aligned measurement. The source's ergotropy interpretation uses Eq. (52); no separate empirical dynamics assertion follows from the covariance theorem.
