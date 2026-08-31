/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden logarithmic scale turns multiplication into translation and multiplication by phi squared into one full shell step. -/

import Mathlib

/-!
The theory uses the positive real scale coordinate `log x / (2 log phi)`.
This file proves its exact multiplicative additivity and the unit translation
caused by multiplication by `phi^2`.  It does not quotient by integers here;
the circle quotient is the semantic projection of this real coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle

open scoped goldenRatio

/-- One orientation-preserving golden scale period. -/
def goldenScalePeriod : ℝ :=
  2 * Real.log Real.goldenRatio

/-- The unwrapped logarithmic coordinate measured in golden periods. -/
def goldenScaleCoordinate (x : ℝ) : ℝ :=
  Real.log x / goldenScalePeriod

/-- The golden period is strictly positive. -/
theorem golden_scale_period_pos : 0 < goldenScalePeriod := by
  unfold goldenScalePeriod
  exact mul_pos (by norm_num) (Real.log_pos Real.one_lt_goldenRatio)

/-- In particular, the golden period is nonzero. -/
theorem golden_scale_period_ne_zero : goldenScalePeriod ≠ 0 :=
  ne_of_gt golden_scale_period_pos

/-- Multiplication of positive scales becomes addition of golden coordinates. -/
theorem golden_scale_coordinate_mul {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    goldenScaleCoordinate (x * y) =
      goldenScaleCoordinate x + goldenScaleCoordinate y := by
  unfold goldenScaleCoordinate
  rw [Real.log_mul hx.ne' hy.ne']
  ring

/-- The logarithm of the orientation-preserving golden unit is exactly one
full golden period. -/
theorem log_golden_ratio_sq_eq_period :
    Real.log (Real.goldenRatio ^ 2) = goldenScalePeriod := by
  rw [pow_two, Real.log_mul Real.goldenRatio_ne_zero
    Real.goldenRatio_ne_zero]
  unfold goldenScalePeriod
  ring

/-- Multiplication by `phi^2` advances the unwrapped coordinate by one shell. -/
theorem golden_scale_coordinate_phi_sq_mul {x : ℝ} (hx : 0 < x) :
    goldenScaleCoordinate (Real.goldenRatio ^ 2 * x) =
      goldenScaleCoordinate x + 1 := by
  rw [golden_scale_coordinate_mul (sq_pos_of_pos Real.goldenRatio_pos) hx,
    goldenScaleCoordinate, log_golden_ratio_sq_eq_period]
  field_simp [golden_scale_period_ne_zero]
  ring

/-- Iterating the orientation-preserving unit advances by the corresponding
natural number of shells. -/
theorem golden_scale_coordinate_phi_even_pow_mul
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    goldenScaleCoordinate ((Real.goldenRatio ^ 2) ^ n * x) =
      goldenScaleCoordinate x + n := by
  induction n with
  | zero => simp [goldenScaleCoordinate]
  | succ n ih =>
      rw [pow_succ', mul_assoc,
        golden_scale_coordinate_phi_sq_mul
          (mul_pos (pow_pos (sq_pos_of_pos Real.goldenRatio_pos) n) hx),
        ih]
      norm_num
      ring

#print axioms golden_scale_period_pos
#print axioms golden_scale_coordinate_mul
#print axioms log_golden_ratio_sq_eq_period
#print axioms golden_scale_coordinate_phi_sq_mul
#print axioms golden_scale_coordinate_phi_even_pow_mul

end D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle
