/- GID: D5/S3/Arith/StephanOddPartPowerDifference
   generality: G
   mirror-B: D5/B/S3/Arith/StephanOddPartPowerDifference
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Field.ZMod, mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.Data.ZMod.Units]
   utility: none
   digest: Stephan's odd-part characterization is equivalent to the A023758 difference form. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Units

namespace D5.S3.Arith.StephanOddPartPowerDifference

def InA181666 (n : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ 3 * ordCompl[2] n + 1 = 4 ^ k

def IsA023758DivThree (n : ℕ) : Prop := ∃ i j : ℕ, j < i ∧ 3 * n + 2 ^ j = 2 ^ i

theorem result (n : ℕ) (_hn : 1 ≤ n) : InA181666 n ↔ IsA023758DivThree n := by
  constructor
  · rintro ⟨k, hk, hodd⟩
    let j := n.factorization 2
    refine ⟨j + 2 * k, j, by omega, ?_⟩
    have hdecomp : 2 ^ j * ordCompl[2] n = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    calc
      3 * n + 2 ^ j = 3 * (2 ^ j * ordCompl[2] n) + 2 ^ j := by rw [hdecomp]
      _ = 2 ^ j * (3 * ordCompl[2] n + 1) := by ring
      _ = 2 ^ j * 4 ^ k := by rw [hodd]
      _ = 2 ^ (j + 2 * k) := by norm_num [pow_add, pow_mul]
  · rintro ⟨i, j, hji, hij⟩
    have hpow : (2 : ZMod 3) ^ j = (2 : ZMod 3) ^ i := by
      have hcast := congrArg (fun x : ℕ => (x : ZMod 3)) hij
      simpa [show (3 : ZMod 3) = 0 by decide] using hcast
    have hfinite : IsOfFinOrder (2 : ZMod 3) :=
      (by decide : IsUnit (2 : ZMod 3)).isOfFinOrder
    have horder : orderOf (2 : ZMod 3) = 2 := by
      rw [CharP.orderOf_eq_two_iff 3 (by norm_num)]
      decide
    have hmod : j ≡ i [MOD 2] := by
      rw [← horder]
      exact hfinite.pow_eq_pow_iff_modEq.mp hpow
    have heven : 2 ∣ i - j := (Nat.modEq_iff_dvd' hji.le).mp hmod
    obtain ⟨k, hk⟩ := heven
    have hi : i = j + (i - j) := by omega
    have hfactor : 3 * n = 2 ^ j * (2 ^ (i - j) - 1) := by
      calc
        3 * n = 2 ^ i - 2 ^ j := Nat.eq_sub_of_add_eq hij
        _ = 2 ^ j * 2 ^ (i - j) - 2 ^ j := by
          conv_lhs => rw [hi, pow_add]
        _ = 2 ^ j * (2 ^ (i - j) - 1) := by
          rw [Nat.mul_sub_left_distrib]
          simp
    have hthree : 3 ∣ 2 ^ (i - j) - 1 := by
      have hprod : 3 ∣ 2 ^ j * (2 ^ (i - j) - 1) := by
        rw [← hfactor]
        exact dvd_mul_right 3 n
      rcases Nat.prime_three.dvd_mul.mp hprod with hbad | hgood
      · exact False.elim ((by norm_num : ¬3 ∣ 2) <| Nat.prime_three.dvd_of_dvd_pow hbad)
      · exact hgood
    obtain ⟨q, hq⟩ := hthree
    have hpowpos : 1 ≤ 2 ^ (i - j) := one_le_pow₀ (by omega)
    have hqeq : 3 * q + 1 = 2 ^ (i - j) := by omega
    have hnq : n = 2 ^ j * q := by
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3)
      calc
        3 * n = 2 ^ j * (2 ^ (i - j) - 1) := hfactor
        _ = 3 * (2 ^ j * q) := by rw [hq]; ring
    have hkpos : 1 ≤ k := by omega
    have hqodd : ¬2 ∣ q := by
      intro htwoq
      obtain ⟨r, hr⟩ := htwoq
      have htwopow : 2 ∣ 2 ^ (i - j) := dvd_pow_self 2 (by omega)
      obtain ⟨s, hs⟩ := htwopow
      omega
    have hord : ordCompl[2] n = q := by
      rw [hnq]
      exact Nat.ordCompl_pow_mul_of_not_dvd j Nat.prime_two hqodd
    refine ⟨k, hkpos, ?_⟩
    rw [hord, hqeq]
    rw [hk]
    norm_num [pow_mul]

end D5.S3.Arith.StephanOddPartPowerDifference
