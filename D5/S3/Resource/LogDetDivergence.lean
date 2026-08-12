/- GID: D5/S3/Resource/LogDetDivergence
   generality: G
   mirror-B: D5/B/S3/Resource/LogDetDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define the log-det barrier height and divergence, with the self-divergence identity. -/

/- The source concerns finite complex Hermitian positive-definite matrices.  This file uses
   `Matrix n n ℂ`; the real-valued encodings take `.re` of the trace and determinant, and the
   dimension is `(Fintype.card n : ℝ)`.  No physical or information-theoretic interpretation is
   claimed here.

   The Bregman link is formalized below with the plus sign: positivity of the determinants makes
   their `.re` values positive real numbers, and determinant multiplicativity plus `Real.log_mul`
   gives the required logarithm identity.  The spectral nonnegativity theorem is NOT proved here;
   the remaining blocker is the similarity/spectral identification of `sigma⁻¹ * rho` with a
   Hermitian positive-definite congruence (and the resulting trace/determinant eigenvalue sum).

   Library-search audit (2026-08-12):
   * `Matrix.PosDef.isUnit` and `Matrix.isUnit_iff_isUnit_det` provide invertibility.
   * `Matrix.nonsing_inv_mul` reduces `rho⁻¹ * rho` to the identity.
   * `Matrix.trace_one`, `Matrix.det_one`, `Complex.ofReal_re`, and `Real.log_one` discharge the
     identity case.  No existing log-det or Bregman-divergence definition was found in the
     repository or in the searched mathlib APIs.
   * The import closure is the umbrella `Mathlib` import (generality `G`). -/

import Mathlib

namespace D5.S3.Resource.LogDetDivergence

open scoped ComplexOrder

noncomputable def barrierHeight {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) : ℝ :=
  -Real.log rho.det.re

noncomputable def logDetDivergence {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) : ℝ :=
  (sigma⁻¹ * rho).trace.re - Real.log ((sigma⁻¹ * rho).det.re)
    - (Fintype.card n : ℝ)

theorem logDetDivergence_self {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) (hρ : rho.PosDef) :
    logDetDivergence rho rho = 0 := by
  fail_if_success ((try simp); done)
  unfold logDetDivergence
  have hdet : IsUnit rho.det := (Matrix.isUnit_iff_isUnit_det rho).mp hρ.isUnit
  rw [Matrix.nonsing_inv_mul rho hdet]
  simp

#print axioms logDetDivergence_self

theorem barrier_bregman_link {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hρ : rho.PosDef) (hσ : sigma.PosDef) :
    logDetDivergence rho sigma =
      barrierHeight rho - barrierHeight sigma + (sigma⁻¹ * (rho - sigma)).trace.re := by
  fail_if_success ((try simp); done)
  have hρdet : 0 < rho.det := hρ.det_pos
  have hσdet : 0 < sigma.det := hσ.det_pos
  have hρdet_eq : rho.det = (rho.det.re : ℂ) := by
    exact Complex.ext rfl hρdet.2.symm
  have hσdet_eq : sigma.det = (sigma.det.re : ℂ) := by
    exact Complex.ext rfl hσdet.2.symm
  have hσunit : IsUnit sigma.det := (Matrix.isUnit_iff_isUnit_det sigma).mp hσ.isUnit
  have hσinvdet : (sigma⁻¹).det = ((sigma.det.re)⁻¹ : ℝ) := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hσdet_eq, Complex.ofReal_inv]
    simp
  have hdet : (sigma⁻¹ * rho).det.re = sigma.det.re⁻¹ * rho.det.re := by
    rw [Matrix.det_mul, hσinvdet, hρdet_eq]
    simp [Complex.mul_re]
  have htrace : (sigma⁻¹ * (rho - sigma)).trace.re =
      (sigma⁻¹ * rho).trace.re - (Fintype.card n : ℝ) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul sigma hσunit, Matrix.trace_sub,
      Matrix.trace_one, Complex.sub_re]
    simp
  unfold logDetDivergence barrierHeight
  rw [hdet, Real.log_mul (inv_ne_zero (ne_of_gt hσdet.1)) (ne_of_gt hρdet.1),
    Real.log_inv]
  rw [htrace]
  ring

#print axioms barrier_bregman_link

/- Nonnegativity remains open: the missing formal step is the similarity/spectral identification
   of `sigma⁻¹ * rho` with a Hermitian positive-definite congruence, together with the resulting
   trace/determinant eigenvalue sum.

A concrete route was located but not taken: mathlib supplies a square root for positive elements
through the continuous functional calculus (`CFC.sqrt`), not as a bespoke `Matrix.sqrt`. The
congruence `sigma^(-1/2) * rho * sigma^(-1/2)` would be built from it; then
`Matrix.PosDef.eigenvalues_pos` and `Matrix.IsHermitian.det_eq_prod_eigenvalues` (both in
`Mathlib/Analysis/Matrix/PosDef.lean`, not in `Mathlib/LinearAlgebra/Matrix/PosDef.lean` where a
search naturally lands) supply the eigenvalue sum, and `Real.log_le_sub_one_of_pos` gives
`x - log x - 1 >= 0` termwise. -/

end D5.S3.Resource.LogDetDivergence
