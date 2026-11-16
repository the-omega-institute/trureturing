/- GID: D5/S1/Recurrence/Parity/DyadicExtendedStirlingEdge
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/DyadicExtendedStirlingEdge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal rational array has binary-weight support and a factorial row edge. -/

import D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
import D5.S1.Digit.KurkovWeightProductBinomial

/-! Binary-weight support and the factorial edge of the literal scalar array. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge

open D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
open D5.S1.Digit.DyadicRowPolynomialRecurrence (wt wt_zero wt_even wt_odd)
open D5.S1.Digit.KurkovWeightProductBinomial (a a_two_pow_mul_odd)

private theorem parent_lt (n : ℕ) (hn : 0 < n) : h n < n := by
  have hi := dyadic_index n hn
  have hp : 0 < 2 ^ g n := by positivity
  have hm := Nat.mul_le_mul_right (2 * h n + 1) (by omega : 1 ≤ 2 ^ g n)
  omega

private theorem weight_parent (n : ℕ) (hn : 0 < n) : wt n = wt (h n) + 1 := by
  conv_lhs => rw [dyadic_index n hn]
  have hw (r m : ℕ) (hm : 0 < m) : wt (2 ^ r * m) = wt m := by
    unfold wt
    rw [Nat.digits_base_pow_mul (b := 2) (by decide) hm]
    simp
  rw [hw _ _ (by omega), wt_odd]

/-- Every column strictly above the binary-weight edge vanishes. -/
theorem support (n k : ℕ) (hk : wt n + 2 < k) : T n k = 0 := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [wt_zero] at hk
      rw [T]
      simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
    · have hp : 0 < n := by omega
      have hw := weight_parent n hp
      rw [dyadic_extended_stirling_block n k (by omega) (by omega),
        ih (h n) (parent_lt n hp) (k - 1) (by omega),
        ih (h n) (parent_lt n hp) k (by omega)]
      ring

/-- OEIS A358612's row-edge conjecture, including the initial row. -/
theorem result (n : ℕ) :
    T n (wt n + 2) = (a n : ℚ) / ((1 + wt n).factorial : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num [wt_zero, T, a]
    · have hp : 0 < n := by omega
      have hw := weight_parent n hp
      have ha : a n = (wt (h n) + 2) ^ (g n + 1) * a (h n) := by
        conv_lhs => rw [dyadic_index n hp]
        exact a_two_pow_mul_odd (g n) (h n)
      rw [dyadic_extended_stirling_block n (wt n + 2) (by omega) (by omega),
        support (h n) (wt n + 2) (by omega), mul_zero, add_zero]
      have hk : wt n + 2 - 1 = wt (h n) + 2 := by omega
      rw [hk, ih (h n) (parent_lt n hp), ha, hw]
      have hf : 1 + (wt (h n) + 1) = (1 + wt (h n)) + 1 := by omega
      rw [hf, Nat.factorial_succ]
      push_cast
      have hfq : ((1 + wt (h n)).factorial : ℚ) ≠ 0 := by positivity
      have hwq : (wt (h n) : ℚ) + 2 ≠ 0 := by positivity
      simp only [pow_succ]
      field_simp
      ring

end D5.S1.Recurrence.Parity.DyadicExtendedStirlingEdge
