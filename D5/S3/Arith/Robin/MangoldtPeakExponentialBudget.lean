/- SOURCE CANDIDATE ONLY. This elementary bound is consumed by the original
   500-scale proof plan. It neither replaces the peak nor shrinks its scope. -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.MangoldtPeakExponentialBudget

/-- The original lower time bound alone pays the final exponential budget.
The elementary second Taylor term avoids an unnecessary logarithm estimate. -/
theorem exponential_dominates (δ D m : ℝ) (hδ : 0 < δ) (hD : 0 < D)
    (hm : 100 * D ^ 2 / δ ^ 2 ≤ m) :
    4000 * m * D ^ 2 < Real.exp (17 * δ * m) := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
  have hmpos : 0 < m := (div_pos (by positivity) hδsq).trans_le hm
  have ht : 100 * D ^ 2 ≤ m * δ ^ 2 := (div_le_iff₀ hδsq).mp hm
  have hprod := mul_le_mul_of_nonneg_right ht hmpos.le
  have hstrict : 0 < m * D ^ 2 := mul_pos hmpos hDsq
  have hquad : 4000 * m * D ^ 2 < (17 * δ * m) ^ 2 / 2 := by
    nlinarith
  have he := Real.pow_div_factorial_le_exp
    (x := 17 * δ * m) (by positivity) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at he
  exact hquad.trans_le he

end D5.S3.Arith.Robin.MangoldtPeakExponentialBudget
