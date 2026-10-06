/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.Construction.Scaling

open D5.S3.Arith.Lattices.Klartag.Construction

namespace D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid

open Matrix
open MeasureTheory
open Metric
open Set

variable {n : ℕ}

/-- `E_A = {v | ⟪A v, v⟫ < 1}`, Klartag eq. (9). -/
def ellipsoid (A : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp < 1}

/-- `Sᵀ A S = 1` forces `det(S)² det(A) = 1`; in particular `S` is invertible. -/
theorem det_sq_mul_det {A S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * A * S = 1) :
    S.det ^ 2 * A.det = 1 := by
  have h := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  linear_combination h

theorem det_ne_zero {A S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * A * S = 1) : S.det ≠ 0 := by
  intro h
  have := det_sq_mul_det hS
  rw [h] at this
  simp at this

/-- The congruence identity for the quadratic form. -/
theorem quad_congr (A S : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    (A *ᵥ (S *ᵥ u)) ⬝ᵥ (S *ᵥ u) = ((Sᵀ * A * S) *ᵥ u) ⬝ᵥ u := by
  have hm : ((A * S)ᵀ * S)ᵀ = Sᵀ * A * S := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
  rw [mulVec_mulVec, dotProduct_mulVec, vecMul_mulVec, ← mulVec_transpose, hm]

theorem quad_congr_one {A S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * A * S = 1) (u : Fin n → ℝ) :
    (A *ᵥ (S *ᵥ u)) ⬝ᵥ (S *ᵥ u) = u ⬝ᵥ u := by
  rw [quad_congr, hS, one_mulVec]

theorem norm_sq_eq_dotProduct (u : EuclideanSpace ℝ (Fin n)) : ‖u‖ ^ 2 = u.ofLp ⬝ᵥ u.ofLp := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [dotProduct, sq]

/-- **Klartag eq. (9): the ellipsoid is the image of the unit ball.** -/
theorem image_ball_eq_ellipsoid {A S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * A * S = 1) :
    (Matrix.toEuclideanLin S) '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 = ellipsoid A := by
  have hunit : IsUnit S.det := (isUnit_iff_ne_zero).2 (det_ne_zero hS)
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hcoe : ((Matrix.toEuclideanLin S) u).ofLp = S *ᵥ u.ofLp := by
      rfl
    have hnorm : ‖u‖ < 1 := by simpa using hu
    have hquad : (A *ᵥ ((Matrix.toEuclideanLin S) u).ofLp) ⬝ᵥ ((Matrix.toEuclideanLin S) u).ofLp
        = ‖u‖ ^ 2 := by rw [hcoe, quad_congr_one hS, ← norm_sq_eq_dotProduct]
    show _ < (1 : ℝ)
    rw [hquad]
    nlinarith [norm_nonneg u]
  · intro hv
    refine ⟨WithLp.toLp 2 (S⁻¹ *ᵥ v.ofLp), ?_, ?_⟩
    · have hu : (WithLp.toLp 2 (S⁻¹ *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin n)).ofLp
          = S⁻¹ *ᵥ v.ofLp := rfl
      have hSv : S *ᵥ (S⁻¹ *ᵥ v.ofLp) = v.ofLp := by
        rw [mulVec_mulVec, Matrix.mul_nonsing_inv S hunit, one_mulVec]
      have hnormsq : ‖(WithLp.toLp 2 (S⁻¹ *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2
          = (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp := by
        rw [norm_sq_eq_dotProduct, hu, ← quad_congr_one hS (S⁻¹ *ᵥ v.ofLp), hSv]
      have : ‖(WithLp.toLp 2 (S⁻¹ *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2 < 1 := by
        rw [hnormsq]; exact hv
      simp only [mem_ball, dist_zero_right]
      nlinarith [norm_nonneg (WithLp.toLp 2 (S⁻¹ *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin n))]
    · apply WithLp.toLp_injective (p := 2)
      simp [Matrix.toEuclideanLin, mulVec_mulVec, Matrix.mul_nonsing_inv S hunit]

/-- **Klartag eq. (10): `Vol(E_A) = det(A)^{-1/2} Vol(Bⁿ)`.** -/
theorem volume_ellipsoid {A S : Matrix (Fin n) (Fin n) ℝ} (hApos : 0 < A.det)
    (hS : Sᵀ * A * S = 1) :
    volume (ellipsoid A)
      = ENNReal.ofReal (1 / Real.sqrt A.det)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have habs : |S.det| = 1 / Real.sqrt A.det := by
    have h := det_sq_mul_det hS
    have hsq : S.det ^ 2 = 1 / A.det := by field_simp; linarith
    have : |S.det| = Real.sqrt (S.det ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    rw [this, hsq, Real.sqrt_div' 1 (le_of_lt hApos)]
    simp [Real.sqrt_one]
  rw [← image_ball_eq_ellipsoid hS,
    MeasureTheory.Measure.addHaar_image_linearMap volume
      (Matrix.toEuclideanLin S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) _,
    LinearMap.det_toLpLin, habs]

/-- **Klartag eq. (68).**  If `√(det A) · D ≤ Vol(Bⁿ)` then the ellipsoid has volume at least
`D`.  The chain supplies `det A_T ≤ C/n⁴`, i.e. `D = c n²`. -/
theorem volume_ellipsoid_ge {A S : Matrix (Fin n) (Fin n) ℝ} (hApos : 0 < A.det)
    (hS : Sᵀ * A * S = 1) {D : ℝ}
    (hdet : Real.sqrt A.det * D
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) :
    ENNReal.ofReal D ≤ volume (ellipsoid A) := by
  have hballtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    (measure_ball_lt_top).ne
  have hsqrt : 0 < Real.sqrt A.det := Real.sqrt_pos.2 hApos
  rw [volume_ellipsoid hApos hS, ← ENNReal.ofReal_toReal hballtop, ← ENNReal.ofReal_mul
    (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hsqrt]
  linarith [hdet]

end D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid
