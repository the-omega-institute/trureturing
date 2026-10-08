/- GID: D5/S3/AnalyticClosure/ComplexPowerDifference
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/ComplexPowerDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform norm bound for the difference of complex powers. -/

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.AnalyticClosure.ComplexPowerDifference

/-- Complex powers have a uniform difference bound on a norm-bounded disk. -/
theorem norm_pow_sub_pow_le (a b : ℂ) (ell : ℕ) (H : ℝ)
    (hH : 0 ≤ H) (ha : ‖a‖ ≤ H) (hb : ‖b‖ ≤ H) :
    ‖a ^ ell - b ^ ell‖ ≤ ell * ‖a - b‖ * H ^ (ell - 1) := by
  rw [← (Commute.all a b).mul_geom_sum₂ ell, norm_mul]
  calc
    ‖a - b‖ * ‖∑ i ∈ Finset.range ell, a ^ i * b ^ (ell - 1 - i)‖ ≤
        ‖a - b‖ * ∑ i ∈ Finset.range ell,
          ‖a ^ i * b ^ (ell - 1 - i)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖a - b‖ * ∑ _i ∈ Finset.range ell, H ^ (ell - 1) := by
      gcongr with i hi
      have hiell : i < ell := Finset.mem_range.mp hi
      rw [norm_mul, norm_pow, norm_pow]
      calc
        ‖a‖ ^ i * ‖b‖ ^ (ell - 1 - i) ≤
            H ^ i * H ^ (ell - 1 - i) := by gcongr
        _ = H ^ (ell - 1) := by
          rw [← pow_add]
          congr 1
          omega
    _ = ell * ‖a - b‖ * H ^ (ell - 1) := by
      simp [mul_assoc, mul_left_comm]

end D5.S3.AnalyticClosure.ComplexPowerDifference
