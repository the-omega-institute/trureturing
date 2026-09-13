/- GID: D5/S3/Arith/Congruence/RationalDenominatorCubeShift
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/RationalDenominatorCubeShift
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.NatAbs, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Residue classes modulo four identify the denominator of a shifted rational cube. -/

import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.RationalDenominatorCubeShift

/-- OEIS A152020: the denominator of `8 / (9 * n^2)`, divided by nine. -/
def a (n : ℕ) : ℕ :=
  (((8 : ℚ) / (9 * (n : ℚ) ^ 2)).den) / 9

private lemma gcd_cube_shift_nat (n : ℕ) (hn : 2 ≤ n) :
    Nat.gcd (n ^ 2) ((n - 2) ^ 3) = Nat.gcd (n ^ 2) 8 := by
  have hlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases hmod : n % 4
  · let m := n / 4
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hnform : n = 4 * m := by dsimp [m]; omega
    have hshift : n - 2 = 2 * (2 * m - 1) := by omega
    have hconsecutive : Nat.Coprime m (m - 1) :=
      (Nat.coprime_self_sub_right hm).mpr (Nat.coprime_one_right m)
    have hnear : Nat.Coprime m (2 * m - 1) := by
      apply Nat.Coprime.symm
      exact (Nat.coprime_sub_self_left (show m ≤ 2 * m - 1 by omega)).mp
        (by simpa only [show 2 * m - 1 - m = m - 1 by omega] using hconsecutive.symm)
    have hcop : Nat.Coprime (2 * m ^ 2) ((2 * m - 1) ^ 3) := by
      apply Nat.Coprime.mul_left
      · exact (Nat.coprime_two_left.mpr ⟨m - 1, by omega⟩).pow_right 3
      · exact hnear.pow 2 3
    rw [hshift, hnform]
    have hsq : (4 * m) ^ 2 = 8 * (2 * m ^ 2) := by ring
    have hcube : (2 * (2 * m - 1)) ^ 3 = 8 * ((2 * m - 1) ^ 3) := by ring
    rw [hsq, hcube, Nat.gcd_mul_left, hcop.gcd_eq_one]
    norm_num [Nat.gcd_eq_right_iff_dvd]
  · let m := n / 4
    have hnform : n = 4 * m + 1 := by dsimp [m]; omega
    have hnodd : Odd n := by rw [hnform]; exact ⟨2 * m, by omega⟩
    have hc2 : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hnodd
    have hshift : Nat.Coprime n (n - 2) :=
      (Nat.coprime_self_sub_right hn).mpr hc2
    have hcop : Nat.Coprime (n ^ 2) ((n - 2) ^ 3) := hshift.pow 2 3
    have hcop8 : Nat.Coprime (n ^ 2) 8 := by
      simpa using hc2.pow 2 3
    rw [hcop.gcd_eq_one, hcop8.gcd_eq_one]
  · let m := n / 2
    have hnform : n = 2 * m := by dsimp [m]; omega
    have hmodd : Odd m := by dsimp [m]; exact ⟨n / 4, by omega⟩
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hshift : n - 2 = 2 * (m - 1) := by omega
    have hconsecutive : Nat.Coprime m (m - 1) :=
      (Nat.coprime_self_sub_right hm).mpr (Nat.coprime_one_right m)
    have hcop2 : Nat.Coprime (m ^ 2) 2 :=
      (Nat.coprime_two_right.mpr hmodd).pow_left 2
    have hcop : Nat.Coprime (m ^ 2) (2 * (m - 1) ^ 3) := by
      apply Nat.Coprime.mul_right
      · exact hcop2
      · exact hconsecutive.pow 2 3
    rw [hshift, hnform]
    have hsq : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
    have hcube : (2 * (m - 1)) ^ 3 = 4 * (2 * (m - 1) ^ 3) := by ring
    rw [hsq, hcube, Nat.gcd_mul_left, hcop.gcd_eq_one]
    rw [show 8 = 4 * 2 by norm_num, Nat.gcd_mul_left, hcop2.gcd_eq_one]
  · let m := n / 4
    have hnform : n = 4 * m + 3 := by dsimp [m]; omega
    have hnodd : Odd n := by rw [hnform]; exact ⟨2 * m + 1, by omega⟩
    have hc2 : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hnodd
    have hshift : Nat.Coprime n (n - 2) :=
      (Nat.coprime_self_sub_right hn).mpr hc2
    have hcop : Nat.Coprime (n ^ 2) ((n - 2) ^ 3) := hshift.pow 2 3
    have hcop8 : Nat.Coprime (n ^ 2) 8 := by
      simpa using hc2.pow 2 3
    rw [hcop.gcd_eq_one, hcop8.gcd_eq_one]

/-- Cicuttin's 2017 conjectured formula for OEIS A152020. -/
theorem cicuttin_a152020 : ∀ n : ℕ, 1 ≤ n →
    a n = (((((n : ℤ) - 2) ^ 3 : ℤ) : ℚ) / (n : ℚ) ^ 2).den := by
  intro n hn
  have hn0 : (n : ℤ) ^ 2 ≠ 0 := by positivity
  have hlq : (8 : ℚ) / (9 * (n : ℚ) ^ 2) =
      Rat.divInt 8 (9 * (n : ℤ) ^ 2) := by
    rw [Rat.divInt_eq_div]
    norm_num
  have hrq : (((((n : ℤ) - 2) ^ 3 : ℤ) : ℚ) / (n : ℚ) ^ 2) =
      Rat.divInt (((n : ℤ) - 2) ^ 3) ((n : ℤ) ^ 2) := by
    rw [Rat.divInt_eq_div]
    norm_num
  have hgcd : Int.gcd ((n : ℤ) ^ 2) (((n : ℤ) - 2) ^ 3) =
      Nat.gcd (n ^ 2) 8 := by
    rcases Nat.eq_or_lt_of_le hn with h | hn'
    · subst n
      norm_num
    · have hn2 : 2 ≤ n := by omega
      have habs : ((n : ℤ) - 2).natAbs = n - 2 := by
        simpa using (Int.natAbs_natCast_sub_natCast_of_ge hn2)
      simp only [Int.gcd_eq_natAbs, Int.natAbs_pow, Int.natAbs_natCast, habs]
      exact gcd_cube_shift_nat n hn2
  have hg9 : Nat.gcd (9 * n ^ 2) 8 = Nat.gcd (n ^ 2) 8 :=
    (show Nat.Coprime 9 8 by norm_num).gcd_mul_left_cancel (n ^ 2)
  have hleft : ((8 : ℚ) / (9 * (n : ℚ) ^ 2)).den =
      9 * (n ^ 2 / Nat.gcd (n ^ 2) 8) := by
    rw [hlq, Rat.den_divInt]
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, hn0, ↓reduceIte,
      Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rw [Int.gcd_eq_natAbs]
    norm_num only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rw [hg9]
    exact Nat.mul_div_assoc 9 (Nat.gcd_dvd_left (n ^ 2) 8)
  have hright : (((((n : ℤ) - 2) ^ 3 : ℤ) : ℚ) / (n : ℚ) ^ 2).den =
      n ^ 2 / Nat.gcd (n ^ 2) 8 := by
    rw [hrq, Rat.den_divInt]
    simp only [hn0, ↓reduceIte, Int.natAbs_pow, Int.natAbs_natCast]
    rw [hgcd]
  have h9 : 9 ∣ ((8 : ℚ) / (9 * (n : ℚ) ^ 2)).den := by
    rw [hleft]
    exact dvd_mul_right 9 _
  rw [a]
  apply (Nat.div_eq_iff_eq_mul_right (by norm_num) h9).mpr
  rw [hleft, hright]

#print axioms cicuttin_a152020

end D5.S3.Arith.Congruence.RationalDenominatorCubeShift
