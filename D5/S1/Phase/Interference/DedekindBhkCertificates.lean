/- GID: D5/S1/Phase/Interference/DedekindBhkCertificates
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/DedekindBhkCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define rational Dedekind sums and certify two finite BHK instances. -/

import D5.S1.Phase.WalkFormula
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace D5.S1.Phase.Interference.DedekindBhkCertificates

open D5.S1.Phase.WalkFormula

/-- The sawtooth function is zero at integers and otherwise is the fractional
part minus one half. -/
def sawtooth (x : Rat) : Rat :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/-- The sawtooth vanishes on every integer. -/
@[simp] theorem sawtooth_int (z : Int) : sawtooth (z : Rat) = 0 := by
  simp [sawtooth]

/-- Adding an integer does not change the sawtooth. -/
theorem sawtooth_add_int (x : Rat) (z : Int) :
    sawtooth (x + z) = sawtooth x := by
  simp [sawtooth]

/-- The rational Dedekind sum over `1 <= k <= c - 1`. -/
def dedekindSum (d c : Nat) : Rat :=
  ∑ k ∈ Finset.Icc 1 (c - 1),
    sawtooth ((k : Rat) / (c : Rat)) *
      sawtooth (((k * d : Nat) : Rat) / (c : Rat))

/-- The Dedekind sum depends on its numerator only modulo the denominator. -/
theorem s_mod (d c : Nat) : dedekindSum (d % c) c = dedekindSum d c := by
  unfold dedekindSum
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  unfold sawtooth
  rw [Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod]
  simp [Nat.mul_mod]

/-- The smallest nontrivial denominator has zero Dedekind sum. -/
theorem dedekind_sum_one_two : dedekindSum 1 2 = 0 := by
  norm_num [dedekindSum, Nat.Icc_eq_range', List.range', sawtooth,
    Int.fract_div_natCast_eq_div_natCast_mod]

/-- The sum for `3/4` is exactly `-1/8`. -/
theorem dedekind_sum_three_four : dedekindSum 3 4 = -1 / 8 := by
  norm_num [dedekindSum, Nat.Icc_eq_range', List.range', sawtooth,
    Int.fract_div_natCast_eq_div_natCast_mod]

/-- The sum for `4/9` is exactly `-4/27`. -/
theorem dedekind_sum_four_nine : dedekindSum 4 9 = -4 / 27 := by
  norm_num [dedekindSum, Nat.Icc_eq_range', List.range', sawtooth,
    Int.fract_div_natCast_eq_div_natCast_mod]

/-- Exact BHK data for the odd normalized continued fraction
`3/4 = [0; 1, 2, 1]`. -/
theorem bhk_three_four_certificate :
    (1 / (1 + 1 / (2 + 1 / 1)) : Rat) = 3 / 4 ∧
      ((3 * 3 : Nat) % 4 = 1) ∧
      alternatingWalk [1, 2, 1] = 0 ∧
      12 * dedekindSum 3 4 =
        -3 + ((3 + 3 : Nat) : Rat) / 4 -
          (alternatingWalk [1, 2, 1] : Rat) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num [alternatingWalk]
  · rw [dedekind_sum_three_four]
    norm_num [alternatingWalk]

/-- Exact BHK data for the longer odd normalized continued fraction
`4/9 = [0; 2, 3, 1]`. -/
theorem bhk_four_nine_certificate :
    (1 / (2 + 1 / (3 + 1 / 1)) : Rat) = 4 / 9 ∧
      ((7 * 4 : Nat) % 9 = 1) ∧
      alternatingWalk [2, 3, 1] = 0 ∧
      12 * dedekindSum 4 9 =
        -3 + ((7 + 4 : Nat) : Rat) / 9 -
          (alternatingWalk [2, 3, 1] : Rat) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num [alternatingWalk]
  · rw [dedekind_sum_four_nine]
    norm_num [alternatingWalk]

example : Nonempty Rat := inferInstance

#print axioms s_mod
#print axioms bhk_three_four_certificate
#print axioms bhk_four_nine_certificate

end D5.S1.Phase.Interference.DedekindBhkCertificates
