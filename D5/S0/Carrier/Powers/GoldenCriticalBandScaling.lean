/- GID: D5/S0/Carrier/Powers/GoldenCriticalBandScaling
   generality: I
   mirror-B: D5/B/S0/Carrier/Powers/GoldenCriticalBandScaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-square scaling maps the second-order band onto a band containing one half. -/

import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace D5.S0.Carrier.Powers.GoldenCriticalBandScaling

/-- Scaling the second-order golden band by the golden square gives the critical-line band. -/
theorem golden_critical_band_scaling :
    And
      ((fun s : Real => Real.goldenRatio ^ 2 * s) ''
          Set.Ioo (1 / (2 * Real.goldenRatio ^ 3)) (1 / Real.goldenRatio ^ 3) =
        Set.Ioo (1 / (2 * Real.goldenRatio)) (1 / Real.goldenRatio))
      (Set.Ioo (1 / (2 * Real.goldenRatio)) (1 / Real.goldenRatio) (1 / 2 : Real)) := by
  constructor
  · convert Set.image_mul_left_Ioo (pow_pos Real.goldenRatio_pos 2)
      (1 / (2 * Real.goldenRatio ^ 3)) (1 / Real.goldenRatio ^ 3) using 1
    all_goals field_simp [Real.goldenRatio_ne_zero]
  · constructor
    · rw [div_lt_div_iff₀ (mul_pos (by norm_num) Real.goldenRatio_pos) (by norm_num)]
      nlinarith [Real.one_lt_goldenRatio]
    · rw [div_lt_div_iff₀ (by norm_num) Real.goldenRatio_pos]
      nlinarith [Real.goldenRatio_lt_two]

example : Nonempty Real := inferInstance

#print axioms golden_critical_band_scaling

end D5.S0.Carrier.Powers.GoldenCriticalBandScaling
