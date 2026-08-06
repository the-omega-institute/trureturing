/- GID: D5/S0/Tower/ConstantArms
   generality: G
   mirror-B: D5/B/S0/Tower/ConstantArms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Radix name towers have exact normalized approximation arms at canonical rational points. -/

import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S0.Tower.ConstantArms

/-- The level-`Q` radix grid consists of the integer multiples of `b ^ (-Q)`. -/
def radixGrid (b Q : ℕ) : Set ℝ :=
  {x | ∃ m : ℤ, x = (m : ℝ) / (b : ℝ) ^ Q}

/-- Distance to the level-`Q` radix grid, realized by rounding after scaling by `b ^ Q`. -/
noncomputable def radixDistance (b Q : ℕ) (x : ℝ) : ℝ :=
  |(b : ℝ) ^ Q * x - (round ((b : ℝ) ^ Q * x) : ℝ)| / (b : ℝ) ^ Q

private theorem scale_mul_radixDistance (b Q : ℕ) (hb : b ≠ 0) (x : ℝ) :
    (b : ℝ) ^ Q * radixDistance b Q x =
      |(b : ℝ) ^ Q * x - (round ((b : ℝ) ^ Q * x) : ℝ)| := by
  rw [radixDistance, mul_div_cancel₀ _ (pow_ne_zero Q (Nat.cast_ne_zero.mpr hb))]

private theorem pow_mod_add_one (b Q : ℕ) (hb : 1 ≤ b) :
    b ^ Q % (b + 1) = 1 ∨ b ^ Q % (b + 1) = b := by
  have hbase : (b : ℤ) ≡ -1 [ZMOD (b + 1 : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    use -1
    ring
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' Q
  · left
    have hInt : ((b ^ (2 * k) : ℕ) : ℤ) ≡ (1 : ℤ) [ZMOD ((b + 1 : ℕ) : ℤ)] := by
      simpa [pow_mul] using hbase.pow (2 * k)
    have hNat : b ^ (2 * k) ≡ 1 [MOD b + 1] := Int.natCast_modEq_iff.mp hInt
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < b + 1)] using hNat
  · right
    have hOdd : ((b ^ (2 * k + 1) : ℕ) : ℤ) ≡ -1 [ZMOD ((b + 1 : ℕ) : ℤ)] := by
      simpa [pow_succ, pow_mul] using hbase.pow (2 * k + 1)
    have hInt : ((b ^ (2 * k + 1) : ℕ) : ℤ) ≡ (b : ℤ) [ZMOD ((b + 1 : ℕ) : ℤ)] :=
      hOdd.trans hbase.symm
    have hNat : b ^ (2 * k + 1) ≡ b [MOD b + 1] := Int.natCast_modEq_iff.mp hInt
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : b < b + 1)] using hNat

/-- The reciprocal of `b + 1` has a constant normalized arm in every nontrivial radix level. -/
theorem constant_arm (b Q : ℕ) (hb : 2 ≤ b) (_hQ : 1 ≤ Q) :
    (b : ℝ) ^ Q * radixDistance b Q ((1 : ℝ) / (b + 1)) = (1 : ℝ) / (b + 1) := by
  rw [scale_mul_radixDistance b Q (by omega : b ≠ 0)]
  have hRound :
      |(b : ℝ) ^ Q * ((1 : ℝ) / (b + 1)) -
          (round ((b : ℝ) ^ Q * ((1 : ℝ) / (b + 1))) : ℝ)| =
        (min (b ^ Q % (b + 1)) (b + 1 - b ^ Q % (b + 1)) : ℕ) / (b + 1) := by
    simpa [div_eq_mul_inv] using
      (abs_sub_round_div_natCast_eq (α := ℝ) (m := b ^ Q) (n := b + 1))
  have hMin : min (b ^ Q % (b + 1)) (b + 1 - b ^ Q % (b + 1)) = 1 := by
    rcases pow_mod_add_one b Q (by omega) with hResidue | hResidue
    · rw [hResidue, show b + 1 - 1 = b by omega, min_eq_left (by omega)]
    · rw [hResidue, show b + 1 - b = 1 by omega, min_eq_right (by omega)]
  rw [hRound, hMin]
  norm_num

/-- In an even radix, the half-radix point has the corresponding constant normalized arm. -/
theorem even_champion_arm (b Q : ℕ) (hb : 2 ≤ b) (_hQ : 1 ≤ Q) (hbEven : Even b) :
    (b : ℝ) ^ Q * radixDistance b Q (((b / 2 : ℕ) : ℝ) / (b + 1)) =
      (b : ℝ) / (2 * (b + 1)) := by
  rcases hbEven with ⟨k, rfl⟩
  have hk : 1 ≤ k := by omega
  have hHalf : (k + k) / 2 = k := by omega
  rw [scale_mul_radixDistance (k + k) Q (by omega : k + k ≠ 0)]
  have hSelf : k * (k + k) ≡ k + 1 [MOD k + k + 1] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨1 - (k : ℤ), ?_⟩
    push_cast
    ring
  have hResidue :
      k * (k + k) ^ Q % (k + k + 1) = k ∨
        k * (k + k) ^ Q % (k + k + 1) = k + 1 := by
    rcases pow_mod_add_one (k + k) Q (by omega) with hPow | hPow
    · left
      have hPowCong : (k + k) ^ Q ≡ 1 [MOD k + k + 1] := by
        simp [Nat.ModEq, hPow, Nat.mod_eq_of_lt (by omega : 1 < k + k + 1)]
      have hCong : k * (k + k) ^ Q ≡ k [MOD k + k + 1] := by
        simpa using hPowCong.mul_left k
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : k < k + k + 1)] using hCong
    · right
      have hPowCong : (k + k) ^ Q ≡ k + k [MOD k + k + 1] := by
        simp [Nat.ModEq, hPow, Nat.mod_eq_of_lt (by omega : k + k < k + k + 1)]
      have hCong : k * (k + k) ^ Q ≡ k + 1 [MOD k + k + 1] :=
        (hPowCong.mul_left k).trans hSelf
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : k + 1 < k + k + 1)] using hCong
  have hMin :
      min (k * (k + k) ^ Q % (k + k + 1))
          (k + k + 1 - k * (k + k) ^ Q % (k + k + 1)) = k := by
    rcases hResidue with hResidue | hResidue
    · rw [hResidue, show k + k + 1 - k = k + 1 by omega, min_eq_left (by omega)]
    · rw [hResidue, show k + k + 1 - (k + 1) = k by omega, min_eq_right (by omega)]
  have hRound :
      |((k + k : ℕ) : ℝ) ^ Q * ((((k + k) / 2 : ℕ) : ℝ) / ((k + k : ℕ) + 1)) -
          (round (((k + k : ℕ) : ℝ) ^ Q *
            ((((k + k) / 2 : ℕ) : ℝ) / ((k + k : ℕ) + 1))) : ℝ)| =
        (min (k * (k + k) ^ Q % (k + k + 1))
          (k + k + 1 - k * (k + k) ^ Q % (k + k + 1)) : ℕ) / (k + k + 1) := by
    simpa [hHalf, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (abs_sub_round_div_natCast_eq (α := ℝ)
        (m := k * (k + k) ^ Q) (n := k + k + 1))
  rw [hRound, hMin]
  field_simp
  push_cast
  ring

/-- The binary one-third arm is the radix-two specialization of `constant_arm`. -/
theorem binary_arm (Q : ℕ) (hQ : 1 ≤ Q) :
    (2 : ℝ) ^ Q * radixDistance 2 Q (1 / 3) = 1 / 3 := by
  have h := constant_arm 2 Q (by norm_num) hQ
  norm_num at h ⊢
  exact h

end D5.S0.Tower.ConstantArms
