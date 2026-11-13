/- GID: D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient
   generality: I
   mirror-B: D5/B/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The six-digit repeating-decimal shift and quotient certificate for one seventh. -/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The two exact rational equalities behind the six-digit period-quotient example.

The theorem deliberately records the arithmetic certificate rather than asserting a
separate analytic definition of an infinite decimal expansion. -/

/-- Shifting six decimal places subtracts the generator `1/7` to expose `142857`. -/
theorem repeating_decimal_142857_shift_quotient :
    (10 : ℚ) ^ 6 * (1 / 7) - (1 / 7) = 142857 ∧
      (142857 : ℚ) / 999999 = 1 / 7 := by
  norm_num

#print axioms repeating_decimal_142857_shift_quotient

end D5.S3.Arith.RepeatingDecimal.RepeatingDecimalQuotient
