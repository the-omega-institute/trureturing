/- GID: D5/S3/Geometry/UnitQuaternions/SU2ExpRemainder
   generality: G
   mirror-B: none(waiver:existing-library-proof-without-a-dedicated-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic ambient remainder for the exponential of an imaginary quaternion. -/

import D5.S3.Geometry.UnitQuaternions.SU2Quantitative

/-! Omega original.

Quadratic ambient remainder for the exponential of an imaginary quaternion.
-/

noncomputable section
open scoped Quaternion Topology
open NormedSpace Set

namespace Omega.Geometry.UnitQuaternion

/-- The chord displacement of a unitary exponential is at most time times speed. -/
theorem exp_chord_le (X : ℍ[ℝ]) (hX : X.re = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • X) - 1‖ ≤ t * ‖X‖ := by
  have hd (s : ℝ) := hasDerivAt_exp_smul_const X s
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    (a := 0) (b := t)
    (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
    (fun s _ => (hd s).hasDerivWithinAt)
    (fun s _ => by rw [norm_mul, norm_exp_smul X hX, one_mul]) t ⟨ht, le_rfl⟩
  simpa [mul_comm] using h

/-- Sharp quadratic remainder, valid globally for nonnegative time. -/
theorem exp_remainder_le (X : ℍ[ℝ]) (hX : X.re = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • X) - 1 - t • X‖ ≤ t ^ 2 * ‖X‖ ^ 2 / 2 := by
  let f (s : ℝ) := exp (s • X) - 1 - s • X
  let v (s : ℝ) := exp (s • X) * X - X
  have hd (s : ℝ) : HasDerivAt f (v s) s := by
    convert ((hasDerivAt_exp_smul_const X s).sub_const 1).sub
      ((hasDerivAt_id s).smul_const X) using 1 <;> first | rfl | simp [v]
  have hv (s : ℝ) (hs : 0 ≤ s) : ‖v s‖ ≤ s * ‖X‖ ^ 2 := by
    dsimp [v]
    rw [show exp (s • X) * X - X = (exp (s • X) - 1) * X by noncomm_ring,
      norm_mul]
    nlinarith [mul_le_mul_of_nonneg_right (exp_chord_le X hX hs) (norm_nonneg X)]
  have hb (s : ℝ) : HasDerivAt (fun r : ℝ => ‖X‖ ^ 2 / 2 * r ^ 2)
      (s * ‖X‖ ^ 2) s := by
    convert ((hasDerivAt_id s).pow 2).const_mul (‖X‖ ^ 2 / 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
    (fun s _ => (hd s).hasDerivWithinAt) (by simp [f]) hb
    (fun s hs => hv s hs.1) (x := t) ⟨ht, le_rfl⟩
  simpa [f, mul_comm, mul_div_assoc] using h

/-- Explicit normalized first-order error, for quantitative ambient transfer. -/
theorem exp_slope_error_le (X : ℍ[ℝ]) (hX : X.re = 0) {t : ℝ} (ht : 0 < t) :
    ‖X - t⁻¹ • (exp (t • X) - 1)‖ ≤ t * ‖X‖ ^ 2 / 2 := by
  have he : X - t⁻¹ • (exp (t • X) - 1) =
      - (t⁻¹ • (exp (t • X) - 1 - t • X)) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  calc
    _ ≤ t⁻¹ * (t ^ 2 * ‖X‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (exp_remainder_le X hX ht.le) (inv_nonneg.mpr ht.le)
    _ = _ := by field_simp

end Omega.Geometry.UnitQuaternion
