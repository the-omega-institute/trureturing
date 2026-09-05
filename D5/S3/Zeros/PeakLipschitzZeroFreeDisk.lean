/- GID: D5/S3/Zeros/PeakLipschitzZeroFreeDisk
   generality: G
   mirror-B: D5/B/S3/Zeros/PeakLipschitzZeroFreeDisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive peak dominates a Lipschitz displacement throughout the strict budget disk, forcing nonvanishing; an affine model has its zero exactly on the boundary. -/

import Mathlib

/- Library-search audit trail (2026-09-04):
   * D5 searches for peak-minus-Lipschitz nonvanishing, zero-free balls,
     Bernstein radius bounds, norm variation, and generalized disk exclusion
     found local analytic-ball machinery but no whole target. The numerical
     `DetectionRadiusCertificate` proves a different logarithmic scale.
   * Pinned Mathlib searches found triangle and Lipschitz primitives, but no
     theorem packaging the strict peak budget with a sharp boundary witness.
     The proof below uses only norm simplification and ordered multiplication. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.PeakLipschitzZeroFreeDisk

/-- If the norm at a center is at least `peak` and the function varies by at
most `slope * distance`, then the strict disk whose full variation budget is
below `peak` contains no zero. Positivity is explicit, so neither a totalized
division nor a zero-radius degeneration can prove the statement silently. -/
theorem strict_peak_lipschitz_zero_free_disk
    (f : ℂ -> ℂ) (center : ℂ) (peak slope radius : ℝ)
    (radius_pos : 0 < radius) (slope_nonneg : 0 ≤ slope)
    (budget : slope * radius < peak)
    (center_peak : peak ≤ ‖f center‖)
    (variation : forall z, dist z center < radius ->
      ‖f z - f center‖ ≤ slope * dist z center) :
    forall z, dist z center < radius -> f z ≠ 0 := by
  have peak_pos : 0 < peak :=
    lt_of_le_of_lt (mul_nonneg slope_nonneg (le_of_lt radius_pos)) budget
  intro z in_disk zero_at_z
  have center_bounded : ‖f center‖ ≤ slope * dist z center := by
    have bound := variation z in_disk
    rw [zero_at_z, zero_sub, norm_neg] at bound
    exact bound
  have scaled_distance : slope * dist z center ≤ slope * radius :=
    mul_le_mul_of_nonneg_left (le_of_lt in_disk) slope_nonneg
  linarith [peak_pos]

/-- The strict radius cannot be enlarged from these hypotheses alone. For
positive `peak` and `slope`, an affine complex function has the prescribed
peak, attains the Lipschitz estimate exactly, and vanishes at distance
`peak / slope` from its center. -/
theorem peak_lipschitz_radius_is_sharp
    (peak slope : ℝ) (peak_pos : 0 < peak) (slope_pos : 0 < slope) :
    let f : ℂ -> ℂ := fun z => (peak : ℂ) - (slope : ℂ) * z
    let boundary : ℂ := ((peak / slope : ℝ) : ℂ)
    ‖f 0‖ = peak ∧
      (forall z, ‖f z - f 0‖ = slope * dist z 0) ∧
      dist boundary 0 = peak / slope ∧ f boundary = 0 := by
  dsimp
  constructor
  · simp [abs_of_pos peak_pos]
  constructor
  · intro z
    rw [show (peak : ℂ) - slope * z - ((peak : ℂ) - slope * 0) =
        -(slope : ℂ) * z by ring]
    simp [abs_of_pos slope_pos, dist_eq_norm]
  constructor
  · rw [dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_of_pos peak_pos, abs_of_pos slope_pos]
  · apply Complex.ext
    · simp
      field_simp [ne_of_gt slope_pos]
      ring
    · simp

#print axioms strict_peak_lipschitz_zero_free_disk
#print axioms peak_lipschitz_radius_is_sharp

end D5.S3.Zeros.PeakLipschitzZeroFreeDisk
