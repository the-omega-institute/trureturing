---
slug: cotfas-2026-uncertainty-condition-conjecture
bibkey: cotfas2026dvgs
doi: 10.48550/arXiv.2610.05623
url: https://arxiv.org/abs/2610.05623v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/CotfasDVGS.result
---

# The uncertainty condition suffices for the mixed discrete Gaussian

## Problem

Nicolae Cotfas, *Frame-dependent coherence of Gaussian quantum states*, arXiv:2610.05623v1, asks after Eq. (22): “As concern ρ̃_σ, we do not know if (11) is sufficient in order to have ρ̃_σ ≥ 0. Based on our numerical investigations, we conjecture that this is true.”

[Preregistration #18946](https://github.com/the-omega-institute/trureturing/issues/18946) fixes the source formulas and quantifiers. [The source note](../Library/QuantumContext/cotfas2026dvgs.md) gives the locators and verbatim statements. The settlement is **Proved** by `D5.S3.Quantum.CotfasDVGS.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Eq. (10), continuous Wigner Gaussian | `W`, real inverse covariance and determinant | Literal formula |
| Odd dimension $d=2s+1\ge3$ | Natural $s$ with $1\le s$ in `claim` | Same range |
| Functions on $\{-s,\ldots,s\}$; addition modulo $d$ | Integer `Finset.Icc` subtype; `ZMod.valMinAbs` | Centered modular representative |
| Eq. (18), displaced parity | `parity`, coefficient in row $m$, column $j$ | Same phase and selected column |
| Eq. (22), signed double lattice sum | `wSum`, `tsum` over $\mathbb Z^2$ | Real division in both coordinates; scalar normalization separated |
| Eq. (21), weighted finite parity sum | `unnormalized` | Both sums use the centered indices |
| $c'_\sigma$ is a normalizing constant | `rhoTilde`, inverse complex trace times `unnormalized` | The proof establishes a nonzero trace |
| Positive Planck parameter | $h\in\mathbb R$, $0<h$ | Universal quantifier |
| Real symmetric positive-definite covariance | Real two-by-two `Matrix.PosDef` | Symmetry follows from this predicate |
| Eq. (11), $\sigma+i\begin{pmatrix}0&1\\-1&0\end{pmatrix}\succeq0$ | The literal complex matrix in `claim` | No certificate replaces the condition |
| Conjectured positivity | `result`: `claim`, including positive semidefiniteness | Exact family |
| Density normalization | Trace equals one in `claim` | Consequence of the source normalization; strengthens positivity |

The public surface comprises `W`, `parity`, `wSum`, `unnormalized`, `rhoTilde`, `claim` and `result`. All other authored declarations are private and have consumers inside this settlement. The centered index type and density conjunction occur literally in the claim; the proof uses existing covariance and density predicates.

## Motivation

A trace-normalized mixed discrete-variable Gaussian can serve as a quantum state when it is positive semidefinite. The theorem supplies that density-operator premise for the exact family in Eqs. (21)–(22), including the determinant-one boundary. It establishes no separate result about coherence quantities or other conclusions of the paper.

## Gap

The source states the sufficiency question explicitly. The literature screen recorded in #18946 covers arXiv:2610.05623v1, the predecessor arXiv:2204.07042v4, INSPIRE citing-work abstracts, indexed MathDB searches and the formal-conjectures snapshot named there. It found no settlement in that scope. Direct MathDB access returned HTTP 403; Feng–Luo, *International Journal of Theoretical Physics* 63, 40 (2024), has a subscription-only main text in which an equivalent result has not been excluded. Literature completeness is **ASSUMED-UNVERIFIED**.

## Route

Write $a=\sigma_{00}$, $c=\sigma_{01}$ and $D=\det\sigma$. The consumed covariance result `GaussianThermometryJointMeasurementRefutation.physical_data` gives $D\ge1$ from the uncertainty condition. `rhoTilde_scaling` reduces the Planck parameter to $d$.

The private `kernel_identity` identifies the unnormalized matrix with twice the integer periodization of

$$K(x,y)=\sqrt{\frac{2}{da}}\exp\!\left(-\frac{\pi((x+y)^2+D(x-y)^2)}{2da}+\frac{i\pi c(x^2-y^2)}{da}\right).$$

The private `half_lattice_poisson` applies Mathlib's `Complex.tsum_exp_neg_quadratic`. The reindexing and Gaussian summability arguments justify the exact signed Wigner construction. `kernel_factorization` writes $K(x,y)=g(x)\overline{g(y)}e^{-\lambda(x-y)^2}$, where $\lambda=\pi(D-1)/(2da)\ge0$. The consumed `FiniteGaussianSchoenberg.gram_gaussian_posSemidef` and the Schur product give finite kernel positivity; closedness gives periodized positivity.

The private `kernel_residual_posSemidef` subtracts a rank-one kernel while preserving positivity. `theta_nonzero` proves upper-half-plane theta nonvanishing by duplication and an eventual small-tail bound. It yields `strongWave_zero_sum_ne_zero`, and hence `periodized_kernel_zero_diagonal_pos`. A positive diagonal entry excludes zero trace. `normalization_isDensity` uses `GHZMeasureBiseparableBound.IsDensity` to complete the density conjunction.

## Falsifier

A covariance satisfying the literal uncertainty condition whose exact infinite-sum matrix has a negative quadratic form or zero trace would contradict the statement. Replacing the signed lattice sum, reversing the parity coefficient convention, or asserting convergence from a finite truncation would change the problem. The Lean result uses the exact formulas and infinite sums.

## Evidence

The mathematical source is [CotfasDVGS.lean](../D5/S3/Quantum/CotfasDVGS.lean), with its [Blueprint](../Blueprint/D5/S3/Quantum/CotfasDVGS.md). The settling GID is `D5/S3/Quantum/CotfasDVGS.result`; its admission basis is `open-problem-resolution (#18946; Proved)`, generality is `I`, and utility is `none`. No fixed-parameter numerical certificate is part of the module. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The escape audit for `D5.S3.Quantum.CotfasDVGS.result` is unfinished: [#19812](https://github.com/the-omega-institute/trureturing/issues/19812). A faithful dependent-family registration lacks a compiled source-reconstruction equivalence bridge, intervention and dependence proofs, and current binding evidence. No Reg mirror or `declared_validated` registration is delivered.

### Declaration classification

The classification expands same-delivery helpers and stops at pinned upstream and existing frozen owners. `theta_nonzero` supplies the nonvanishing argument on the live path through `strongWave_zero_sum_ne_zero` and `periodized_kernel_zero_diagonal_pos` to `result`. Dependency identities and direct consumers are extracted from compiled proof terms and the scoped Lean report.

| module | declaration | proof_shape | escape_witness | consumers | direct frozen dependencies |
| --- | --- | --- | --- | --- | --- |
| `D5/S3/Quantum/CotfasDVGS` | `D5.S3.Quantum.CotfasDVGS.result` (`sha256:76e6c7d115fcc90748ee7baeb5a85a1ba9c04094d72192d23281e83188ec404c`) | content | `D5.S3.Quantum.CotfasDVGS.theta_nonzero` | settlement | `D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation` + `D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov` + `sha256:410391e348afb0d9876bdf2548ca1782f14191e2ac259dd3c3d81d1876de06a4`<br>`D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation` + `D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.physical_data` + `sha256:5cca2636075e308d2c7601cbf4eec201deeff36ae84f87cba8d1efbc1a1c4ec9`<br>`D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation` + `D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.thermalCov._proof_1` + `sha256:83f1ceeb429672fc69ed7b05221717bed36bfc3d20bfbfaf29d42aff28260770`<br>`D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound` + `D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity` + `sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448`<br>`D5/S3/Weil/Probability/FiniteGaussianSchoenberg` + `D5.S3.Weil.Probability.FiniteGaussianSchoenberg.gram_gaussian_posSemidef` + `sha256:e83ee5619019d4fc81d7390a8b36152737f3dda0b497486e0e5fc9c97d9a1c91` |

| helper (full Lean name) | proof_shape | escape_witness | direct consumers |
| --- | --- | --- | --- |
| `D5.S3.Quantum.CotfasDVGS.W` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.W_coordinates`, `D5.S3.Quantum.CotfasDVGS.W_gaussian_bound`, `D5.S3.Quantum.CotfasDVGS.W_nonnegative`, `D5.S3.Quantum.CotfasDVGS.W_scaling`, `D5.S3.Quantum.CotfasDVGS.entry_half_lattice`, `D5.S3.Quantum.CotfasDVGS.kernel_fourier_slice`, `D5.S3.Quantum.CotfasDVGS.kernel_identity`, `D5.S3.Quantum.CotfasDVGS.signed_W_lattice_summable`, `D5.S3.Quantum.CotfasDVGS.wSum`, `D5.S3.Quantum.CotfasDVGS.wSum_scaling` |
| `D5.S3.Quantum.CotfasDVGS.parity` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.unnormalized`, `D5.S3.Quantum.CotfasDVGS.unnormalized_entry_midpoint`, `D5.S3.Quantum.CotfasDVGS.unnormalized_scaling` |
| `D5.S3.Quantum.CotfasDVGS.wSum` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.entry_half_lattice`, `D5.S3.Quantum.CotfasDVGS.unnormalized`, `D5.S3.Quantum.CotfasDVGS.unnormalized_entry_midpoint`, `D5.S3.Quantum.CotfasDVGS.unnormalized_scaling`, `D5.S3.Quantum.CotfasDVGS.wSum_scaling` |
| `D5.S3.Quantum.CotfasDVGS.unnormalized` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.entry_half_lattice`, `D5.S3.Quantum.CotfasDVGS.kernel_identity`, `D5.S3.Quantum.CotfasDVGS.result`, `D5.S3.Quantum.CotfasDVGS.rhoTilde`, `D5.S3.Quantum.CotfasDVGS.rhoTilde_scaling`, `D5.S3.Quantum.CotfasDVGS.unnormalized_entry_midpoint`, `D5.S3.Quantum.CotfasDVGS.unnormalized_scaling` |
| `D5.S3.Quantum.CotfasDVGS.rhoTilde` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.claim`, `D5.S3.Quantum.CotfasDVGS.result`, `D5.S3.Quantum.CotfasDVGS.rhoTilde_scaling` |
| `D5.S3.Quantum.CotfasDVGS.claim` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.W_scaling` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.wSum_scaling` |
| `D5.S3.Quantum.CotfasDVGS.wSum_scaling` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.unnormalized_scaling` |
| `D5.S3.Quantum.CotfasDVGS.unnormalized_scaling` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.rhoTilde_scaling` |
| `D5.S3.Quantum.CotfasDVGS.rhoTilde_scaling` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.uncertainty_det_bound` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.normalization_isDensity` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.kernel` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.finite_periodization_posSemidef`, `D5.S3.Quantum.CotfasDVGS.kernel_factorization`, `D5.S3.Quantum.CotfasDVGS.kernel_fourier_slice`, `D5.S3.Quantum.CotfasDVGS.kernel_identity`, `D5.S3.Quantum.CotfasDVGS.kernel_lattice_summable`, `D5.S3.Quantum.CotfasDVGS.kernel_norm_bound`, `D5.S3.Quantum.CotfasDVGS.kernel_posSemidef`, `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef`, `D5.S3.Quantum.CotfasDVGS.periodization_posSemidef`, `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos`, `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.wave` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_factorization`, `D5.S3.Quantum.CotfasDVGS.kernel_posSemidef`, `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef`, `D5.S3.Quantum.CotfasDVGS.strongWave_factorization` |
| `D5.S3.Quantum.CotfasDVGS.kernel_factorization` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_posSemidef`, `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef` |
| `D5.S3.Quantum.CotfasDVGS.lambda_nonnegative` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_posSemidef`, `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef` |
| `D5.S3.Quantum.CotfasDVGS.finite_gaussian_posSemidef` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.finite_gaussian_residual_posSemidef`, `D5.S3.Quantum.CotfasDVGS.kernel_posSemidef` |
| `D5.S3.Quantum.CotfasDVGS.kernel_posSemidef` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.finite_periodization_posSemidef` |
| `D5.S3.Quantum.CotfasDVGS.sum_subtype_pair` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.finite_periodization_posSemidef`, `D5.S3.Quantum.CotfasDVGS.lattice_sum_nonnegative` |
| `D5.S3.Quantum.CotfasDVGS.finite_periodization_posSemidef` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.periodization_posSemidef` |
| `D5.S3.Quantum.CotfasDVGS.periodization_posSemidef` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.gaussian_shifted_summable` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_lattice_summable`, `D5.S3.Quantum.CotfasDVGS.signed_W_lattice_summable`, `D5.S3.Quantum.CotfasDVGS.strongWave_summable` |
| `D5.S3.Quantum.CotfasDVGS.kernel_norm_bound` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_lattice_summable` |
| `D5.S3.Quantum.CotfasDVGS.kernel_lattice_summable` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_identity`, `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos`, `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.centered_eq_of_dvd` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.halfLatticeMap_injective`, `D5.S3.Quantum.CotfasDVGS.midpoint_unique` |
| `D5.S3.Quantum.CotfasDVGS.halfLatticeMap` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.halfLatticeEquiv`, `D5.S3.Quantum.CotfasDVGS.halfLatticeMap_injective`, `D5.S3.Quantum.CotfasDVGS.halfLatticeMap_surjective`, `D5.S3.Quantum.CotfasDVGS.midpoint_exists` |
| `D5.S3.Quantum.CotfasDVGS.halfLatticeMap_injective` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.halfLatticeEquiv` |
| `D5.S3.Quantum.CotfasDVGS.valMinAbs_sub_dvd` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.halfLatticeMap_surjective`, `D5.S3.Quantum.CotfasDVGS.midpoint_unique` |
| `D5.S3.Quantum.CotfasDVGS.halfLatticeMap_surjective` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.halfLatticeEquiv`, `D5.S3.Quantum.CotfasDVGS.midpoint_exists` |
| `D5.S3.Quantum.CotfasDVGS.halfLatticeEquiv` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.entry_half_lattice` |
| `D5.S3.Quantum.CotfasDVGS.inverse_quadratic_coordinates` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.W_coordinates`, `D5.S3.Quantum.CotfasDVGS.inverse_quadratic_lower_bound` |
| `D5.S3.Quantum.CotfasDVGS.W_coordinates` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_fourier_slice` |
| `D5.S3.Quantum.CotfasDVGS.inverse_quadratic_lower_bound` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.W_gaussian_bound` |
| `D5.S3.Quantum.CotfasDVGS.half_lattice_poisson` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_fourier_slice` |
| `D5.S3.Quantum.CotfasDVGS.theta_series_summable` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.theta_duplication` |
| `D5.S3.Quantum.CotfasDVGS.exp_pi_int` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.phase_half_lattice`, `D5.S3.Quantum.CotfasDVGS.theta_term_shift` |
| `D5.S3.Quantum.CotfasDVGS.neg_one_int_square` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.theta_term_shift` |
| `D5.S3.Quantum.CotfasDVGS.theta_term_shift` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.theta_duplication` |
| `D5.S3.Quantum.CotfasDVGS.parityLatticeMap` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.parityLatticeMap_injective`, `D5.S3.Quantum.CotfasDVGS.theta_duplication` |
| `D5.S3.Quantum.CotfasDVGS.parityLatticeMap_injective` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.theta_duplication` |
| `D5.S3.Quantum.CotfasDVGS.theta_duplication` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.theta_nonzero` |
| `D5.S3.Quantum.CotfasDVGS.theta_nonzero_small` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.theta_nonzero` |
| `D5.S3.Quantum.CotfasDVGS.theta_nonzero` | content | `D5.S3.Quantum.CotfasDVGS.theta_nonzero` | `D5.S3.Quantum.CotfasDVGS.strongWave_zero_sum_ne_zero` |
| `D5.S3.Quantum.CotfasDVGS.W_nonnegative` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.signed_W_lattice_summable` |
| `D5.S3.Quantum.CotfasDVGS.W_gaussian_bound` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.signed_W_lattice_summable` |
| `D5.S3.Quantum.CotfasDVGS.signed_W_lattice_summable` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.entry_half_lattice` |
| `D5.S3.Quantum.CotfasDVGS.midpoint_exists` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_identity` |
| `D5.S3.Quantum.CotfasDVGS.parity_support` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.unnormalized_entry_midpoint` |
| `D5.S3.Quantum.CotfasDVGS.midpoint_unique` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.unnormalized_entry_midpoint` |
| `D5.S3.Quantum.CotfasDVGS.gaussian_fourier_term` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_fourier_slice` |
| `D5.S3.Quantum.CotfasDVGS.kernel_fourier_slice` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_identity` |
| `D5.S3.Quantum.CotfasDVGS.finite_gaussian_residual_posSemidef` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef` |
| `D5.S3.Quantum.CotfasDVGS.strongWave` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef`, `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos`, `D5.S3.Quantum.CotfasDVGS.strongWave_factorization`, `D5.S3.Quantum.CotfasDVGS.strongWave_norm`, `D5.S3.Quantum.CotfasDVGS.strongWave_summable`, `D5.S3.Quantum.CotfasDVGS.strongWave_zero_sum_ne_zero` |
| `D5.S3.Quantum.CotfasDVGS.strongWave_factorization` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef` |
| `D5.S3.Quantum.CotfasDVGS.kernel_residual_posSemidef` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos` |
| `D5.S3.Quantum.CotfasDVGS.strongWave_norm` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.strongWave_summable` |
| `D5.S3.Quantum.CotfasDVGS.strongWave_summable` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos` |
| `D5.S3.Quantum.CotfasDVGS.strongWave_zero_sum_ne_zero` | content | `D5.S3.Quantum.CotfasDVGS.theta_nonzero` | `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos` |
| `D5.S3.Quantum.CotfasDVGS.lattice_sum_nonnegative` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos` |
| `D5.S3.Quantum.CotfasDVGS.periodized_kernel_zero_diagonal_pos` | content | `D5.S3.Quantum.CotfasDVGS.theta_nonzero` | `D5.S3.Quantum.CotfasDVGS.result` |
| `D5.S3.Quantum.CotfasDVGS.kernelLatticeEquiv` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_identity` |
| `D5.S3.Quantum.CotfasDVGS.phase_half_lattice` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.entry_half_lattice` |
| `D5.S3.Quantum.CotfasDVGS.unnormalized_entry_midpoint` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.entry_half_lattice` |
| `D5.S3.Quantum.CotfasDVGS.entry_half_lattice` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.kernel_identity` |
| `D5.S3.Quantum.CotfasDVGS.kernel_identity` | bind-only | `none` | `D5.S3.Quantum.CotfasDVGS.result` |

### Numerical experiment

[Experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/04bafcea983207a1fa6056376aa68d57319d2fa1/docs/reports/cotfas-2026-discrete-gaussian-positivity), commit `04bafcea983207a1fa6056376aa68d57319d2fa1`:

- `python3 check.py`, run from that directory, exits 0. Script SHA-256: `e590d9f1a35641dad4b659163e4b678ad34a5857beb62032952007133fa0181b`. It checks 600 covariances with $D\ge1$, including determinant-one samples, at $d\in\{1,3,5,7,9\}$ and $h\in\{0.5,1,3\}$ with lattice cutoff 40: zero failures, worst relative minimum eigenvalue $-7.668186032229494\times10^{-16}$. All 36 sampled $D<1$ cases are non-PSD.
- `python3 identity.py`, run from that directory, exits 0. Script SHA-256: `9121d2a4c4a9479e0c28235bce7e4b10dabb256302626e7ac6bf3e29ff48647c`. The entrywise kernel-identity error is at most $1.6514567491299204\times10^{-15}$ for $d\in\{3,5,7\}$ and four covariances.

These are numerical computations on truncated sums, not uniform proofs or a necessity theorem.

## Triage

| Item | Status | Evidence and scope |
| --- | --- | --- |
| Settlement | Proved, kernel-checked | `D5.S3.Quantum.CotfasDVGS.result`, exactly the binding conventions and $s\ge1$, $h>0$ |
| Mechanism | Proved, kernel-checked | Private `kernel_identity`, `kernel_factorization`, `kernel_residual_posSemidef`, `theta_nonzero` and `periodized_kernel_zero_diagonal_pos` on `result`'s path |
| Determinant boundary | Proved, kernel-checked | `result` uses $D\ge1$ uniformly; both $D=1$ and $D>1$ are included |
| Necessity | Open | The 36 sub-bound examples are computed by the pinned `check.py` above; they do not establish necessity for the discrete matrix |
| Dimension one | Open in this delivery | Numerical $d=1$ samples are computed above; the delivered theorem retains $s\ge1$ and makes no separate $d=1$ claim |
| Novelty and literature completeness | Open; ASSUMED-UNVERIFIED | Classical Gaussian, Poisson and theta ingredients carry no originality claim; the Feng–Luo main text is not excluded |

### What the settlement shows

**Proved, kernel-checked.** The nonnegative uncertainty defect controls the Gaussian Gram factor, while a rank-one residual bound and theta nonvanishing give strict diagonal positivity. This handles $D=1$ and $D>1$ in the same argument. The exact normalized matrix is a density operator throughout the source's stated family.

**Explanation from the factorization.** At $D=1$, $\lambda=0$ and the Gaussian factor is one; thus the displayed kernel is $g(x)\overline{g(y)}$. The parameter entering the exponential damping is $\pi(D-1)/(2da)$; no equality between $D-1$ alone and a mixing variance is asserted.

**Open.** Necessity of the uncertainty condition for the discrete matrix, a separate dimension-one theorem, weaker covariance hypotheses, sharpness beyond the source family, and additional coherence results are not settled here. The paper's uses of these matrices obtain their density-operator premise under the hypotheses of `result`; no other source theorem is certified by this delivery.

## ASSUMED-UNVERIFIED

Literature-search completeness, including the subscription-only Feng–Luo text, remains unverified. No originality of the classical ingredients is claimed. The escape registration remains unfinished under #19812. Finite numerical checks have only the tested scope specified above.
