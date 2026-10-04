---
slug: cenni-lami-acin-mehboudi-2022-gaussian-thermometry-local-global-refutation
bibkey: cenni2022gaussianthermometry
doi: null
url: https://arxiv.org/abs/2110.02098v4
triage: theorem
motivation_gids:
  - D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.result
---

# Local versus joint Gaussian thermometry for unequal-frequency modes

## Problem

M. F. B. Cenni, L. Lami, A. Acín and M. Mehboudi, “Thermometry of Gaussian
quantum systems using Gaussian measurements”, arXiv:2110.02098v4, §3.2,
Eq. (47), ask whether the optimal joint Gaussian Fisher information equals
the optimal local Gaussian Fisher information for every product thermal state:

> "${\cal F}^{\rm C}(\oplus_k {\bm \sigma}_{k}; {\bm \sigma}^M_{\max}) \overset{?}{=} {\cal F}^{\rm C}(\oplus_k {\bm \sigma}_{k}; \oplus_k{\bm \sigma}_{k,\max}^M)$"

> Based on these observations we conjecture this is generally true, however, a rigorous proof is missing currently.

Issue [#11666](https://github.com/the-omega-institute/trureturing/issues/11666)
preregisters this Tier 1 conjecture, the quantified version 2 and the two-mode
counterexample. The formal claim compares each physical joint value with the
supremum over all physical block-diagonal measurements.

## Motivation

For m independent thermal modes at a common temperature T > 0 and frequencies
ωk > 0, set νk = coth(ωk/(2T)), νk′ = (ωk/(2T²))(νk²−1),
σ = ⊕k νk I₂ and ∂Tσ = ⊕k νk′ I₂. For a real symmetric measurement covariance
Γ with Γ+iΩ positive semidefinite, p. 6 §3.2.2, Eq. (36) gives
F = ½ tr[((σ+Γ)⁻¹ ∂Tσ)²]. Define localFisher as the supremum of these values
for Γ = ⊕k Mk, where each 2×2 Mk is symmetric and Mk+iJ is positive
semidefinite. The definition includes every mixed block and every rotation.
The formal claim universally bounds each admissible joint covariance by
localFisher, for all m, positive frequencies and positive T.

## Gap

The v4 source states the conjecture and proves the identical-covariance case.
The literature scope recorded in #11666 includes arXiv:2512.20534, whose
identical-copy/equal-symplectic-eigenvalue result does not cover ν₁=2 and
ν₂=5/4, and the other thermometry papers listed there. No settlement is found
in that searched scope. Citation-index completeness is ASSUMED-UNVERIFIED;
this statement is neither an exhaustive literature claim nor a priority claim.

## Route

Use m=2, T=1 and a=artanh(1/2)>0, with frequencies (2a,4a), equivalently
(ln 3,2 ln 3). The thermal eigenvalues are (2,5/4) and their derivatives
are (3a,9a/8). In interleaved q,p coordinates choose

S = (1/5)[[13,0,12,0],[0,13,0,−12],[12,0,13,0],[0,−12,0,13]],
Γ = SSᵀ = (1/25)[[313,0,312,0],[0,313,0,−312],
                  [312,0,313,0],[0,−312,0,313]].

A complex Gram factorization certifies Γ+iΩ positive semidefinite. A rational
right-inverse certificate computes (σ+Γ)⁻¹ and gives
F = (1493661/964324)a² = (1493661/3857296)(ln 3)².

For a physical single-mode covariance M, the uncertainty matrix implies
M positive definite and det M ≥ 1. Set P=M/√det M. Then det P=1,
P+iJ is positive semidefinite by an explicit complex Gram certificate,
and M−P is positive semidefinite. P is pure; its eigenvalues are r and 1/r
for r ≥ 1, and its trace t=r+1/r ≥ 2 is independent of the orientation.

The inverse-order proof uses, for positive definite A and B with C=B−A ≥ 0,

B(A⁻¹−B⁻¹)B = CA⁻¹C+C ≥ 0.

Congruence yields A⁻¹−B⁻¹ ≥ 0. The nonnegative trace of a product of
positive semidefinite matrices then bounds tr(B⁻²) by tr(A⁻²).
Consequently F(νI,dI;M) ≤ F(νI,dI;P) for every ν>0 and real d.

For pure P, put D=ν²+νt+1 and N=(2ν+t)²−2D. The exact inverse certificate
gives F(νI,dI;P)=(d²/2)N/D². The rational certificates are

- ν=2: D²/4−N=t+1/4 ≥ 0, hence F ≤ d²/8.
- ν=5/4: (16/25)D²−N=(8/5)t+1231/400 ≥ 0, hence F ≤ (8/25)d².

Additivity of the two block values gives, for every physical local measurement,

F ≤ (3a)²/8 + (8/25)(9a/8)² = (153/100)a².

The identity covariance supplies a member of the local set. Its nonempty
supremum is therefore at most (153/400)(ln 3)². The explicit joint value
exceeds this bound by (114033/24108100)(ln 3)² > 0, refuting claim.
The covariance and derivative use Fin.cast(...).divNat for the mode index;
Ω is the interleaved-coordinate submatrix of −Mathlib Matrix.J.

## Falsifier

The claim retains positive frequencies and temperature, real symmetry and
the complex positive-semidefinite measurement condition. The witness meets
all antecedents. A covariance violating uncertainty or a bound holding only
for a chosen local block would not refute this claim. The comparison is
covariance-only, with zero displacement; the equal-mode special case is
outside the counterexample.

## Evidence

The public definitions are thermalNuDeriv, thermalCov, thermalCovDeriv,
IsGaussianMeasurementCov, fisherC, localCov, localFisher and claim.
The sole public theorem is result : ¬ claim. The private theorem
single_mode_local_bound is escape witness v2: it proves the per-mode bounds
and invertibility used by the additive local bound inside result. Its
monotonicity, uncertainty-to-purity and exact rational certificate steps
are local have proofs; the remaining proof steps are inside result.
Both the private theorem and result have proof_shape content. The direct
frozen dependencies are D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.coth
and D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef.
The latter supplies the nonnegative product trace in the monotonicity proof.
The admission basis is open-problem-resolution (#11666; Refuted), with the
certified refutation utility header. Information-escape registration is
paused under CLAUDE.md §3.9.

## Triage

Tier 1: a published explicit conjecture, refuted for two unequal-frequency
modes under quantified version 2.

### What the settlement shows

- Proved: single-mode Loewner monotonicity for every ν>0 and real derivative d;
  every physical single-mode covariance dominates a physical pure one.
- Proved: the rational per-mode bounds hold for every physical covariance,
  including every pure squeezing parameter r ≥ 1 and every rotation, at
  ν=2 and ν=5/4. The module does not prove the optimal bound for every ν.
- Proved: two-block additivity, the local set's nonemptiness and its supremum
  bound, all on the live refutation path. The local-optimization bridge at
  the witness is kernel-checked and has no unproved premise.
- Proved: positive witness frequencies and temperature, joint admissibility,
  thermal values (2,5/4), the joint value and its strict excess over localFisher.
- Literature result that survives: the identical-mode theorem and the source's
  separate single-mode result are compatible with the unequal-mode counterexample.
- Open: locality-optimal unequal-frequency states, the full two-mode joint
  optimum and higher-mode sharp gains. Conclusions conditional on Eq. (47)
  for arbitrary products require that condition or a restricted replacement.

## ASSUMED-UNVERIFIED

Citation indices are incomplete as recorded in #11666. The source-to-model
interpretation remains a literature and fidelity-review obligation; the
local optimization bound at the witness itself is Lean-proved.
