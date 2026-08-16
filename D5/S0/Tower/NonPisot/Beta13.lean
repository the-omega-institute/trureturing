/- GID: D5/S0/Tower/NonPisot/Beta13
   generality: G
   mirror-B: D5/B/S0/Tower/NonPisot/Beta13
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The quadratic base beta13 has a conjugate whose modulus is greater than one. -/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace D5.S0.Tower.NonPisot.Beta13

/- Library search receipt:
   * No existing D5 declaration defines the root of x^2 - x - 3.
   * Mathlib's `Nat.Prime.irrational_sqrt` supplies the exact irrationality input for sqrt 13. -/

/-- The positive root of `x^2 - x - 3`. -/
noncomputable def beta13 : Real := (1 + Real.sqrt 13) / 2

/-- The other real root of `x^2 - x - 3`. -/
noncomputable def beta13Conjugate : Real := (1 - Real.sqrt 13) / 2

/-- The defining quadratic identity for `beta13`. -/
theorem beta13_sq : beta13 ^ 2 = beta13 + 3 := by
  have hsqrt : Real.sqrt (13 : Real) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  rw [beta13]
  nlinarith

/-- The base lies strictly between two and three. -/
theorem beta13_between_two_three : 2 < beta13 ∧ beta13 < 3 := by
  have hsqrt : Real.sqrt (13 : Real) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 <= Real.sqrt (13 : Real) := Real.sqrt_nonneg 13
  have hsqrtLower : 3 < Real.sqrt (13 : Real) := by nlinarith
  have hsqrtUpper : Real.sqrt (13 : Real) < 5 := by nlinarith
  rw [beta13]
  constructor <;> nlinarith

/-- The conjugate has modulus strictly greater than one. -/
theorem beta13_conjugate_abs_gt_one : 1 < |beta13Conjugate| := by
  have hsqrt : Real.sqrt (13 : Real) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 <= Real.sqrt (13 : Real) := Real.sqrt_nonneg 13
  have hsqrtLower : 3 < Real.sqrt (13 : Real) := by nlinarith
  have hconjugateNeg : beta13Conjugate < 0 := by
    rw [beta13Conjugate]
    nlinarith
  rw [abs_of_neg hconjugateNeg, beta13Conjugate]
  nlinarith

/-- Irrationality of the base makes its integral two-coordinate representation unique. -/
theorem beta13_irrational : Irrational beta13 := by
  have hsqrt := Nat.Prime.irrational_sqrt (show Nat.Prime 13 by norm_num)
  have hshifted := hsqrt.ratCast_add 1
  convert! hshifted.ratCast_mul (show (0.5 : ℚ) ≠ 0 by norm_num)
  simp [beta13]
  ring

end D5.S0.Tower.NonPisot.Beta13
