/- GID: D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: The average of a twin prime pair has no superdivisor. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.GerasimovTwinPrimeMeanNoSuperdivisor

/-- A divisor `k` is a superdivisor of `n` when all three divisibility
conditions in OEIS A247477 hold, with `d = n / k`. -/
def IsSuperdivisor (n k : ℕ) : Prop :=
  (n / k + n) ∣ ((n / k) ^ (n / k) + n) ∧
    (n / k + n) ∣ ((n / k) ^ n + n / k) ∧
      (n / k + n) ∣ (n ^ (n / k) + n / k)

private theorem no_superdivisor_of_even_and_pred_prime
    {n : ℕ} (hn : 4 ≤ n) (hn_even : Even n) (hprime : Nat.Prime (n - 1)) :
    ∀ k : ℕ, 1 ≤ k → k ∣ n → ¬ IsSuperdivisor n k := by
  intro k hkpos hkdiv hsuper
  let d := n / k
  have hdk : d * k = n := by
    simpa only [d] using Nat.div_mul_cancel hkdiv
  have hdpos : 0 < d := by
    by_contra hdnot
    have hdzero : d = 0 := Nat.eq_zero_of_not_pos hdnot
    rw [hdzero, zero_mul] at hdk
    omega
  rcases hsuper with ⟨hfirst, hsecond, _⟩
  change d + n ∣ d ^ d + n at hfirst
  change d + n ∣ d ^ n + d at hsecond
  have hpow_d : d ^ d = d * d ^ (d - 1) := by
    calc
      d ^ d = d ^ (d - 1 + 1) := by
        congr 1
        omega
      _ = d ^ (d - 1) * d := by rw [pow_succ]
      _ = d * d ^ (d - 1) := Nat.mul_comm _ _
  have hpow_n : d ^ n = d * d ^ (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  have hfirst' : k + 1 ∣ d ^ (d - 1) + k := by
    apply (Nat.mul_dvd_mul_iff_left hdpos).mp
    rw [Nat.mul_add, Nat.mul_one, hdk, Nat.add_comm]
    rw [Nat.mul_add, ← hpow_d, hdk]
    exact hfirst
  have hsecond' : k + 1 ∣ d ^ (n - 1) + 1 := by
    apply (Nat.mul_dvd_mul_iff_left hdpos).mp
    rw [Nat.mul_add, Nat.mul_one, hdk, Nat.add_comm]
    rw [Nat.mul_add, Nat.mul_one, ← hpow_n]
    exact hsecond
  rcases eq_or_ne k 1 with rfl | hkone
  · have hd_eq_n : d = n := by simpa using hdk
    subst d
    have hcast : ((n ^ (n - 1) + 1 : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (by simpa using hfirst')
    have hncast : (n : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (even_iff_two_dvd.mp hn_even)
    norm_num [Nat.cast_add, Nat.cast_pow, hncast, zero_pow (by omega : n - 1 ≠ 0)] at hcast
  · rcases eq_or_ne d 1 with hdone | hdone
    · rw [hdone, one_mul] at hdk
      norm_num [hdone, hdk] at hsecond'
      have := Nat.le_of_dvd (by decide : 0 < 2) hsecond'
      omega
    · have hk : 2 ≤ k := by omega
      have hd : 2 ≤ d := by omega
      let m := k + 1
      let P := n - 1
      let x : ZMod m := d
      have hm : 2 < m := by dsimp [m]; omega
      have hPprime : Nat.Prime P := by simpa only [P] using hprime
      have hkcast : (k : ZMod m) = -1 := by
        have hself : ((m : ℕ) : ZMod m) = 0 := ZMod.natCast_self m
        change (k : ZMod m) = -1
        simpa only [m, Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg] using hself
      have hpow_one : x ^ (d - 1) = 1 := by
        have hzero : ((d ^ (d - 1) + k : ℕ) : ZMod m) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).2 (by simpa only [m] using hfirst')
        change (d : ZMod m) ^ (d - 1) = 1
        rw [Nat.cast_add, Nat.cast_pow, hkcast] at hzero
        exact (add_neg_eq_zero.mp hzero)
      have hpow_neg : x ^ P = -1 := by
        have hzero : ((d ^ (n - 1) + 1 : ℕ) : ZMod m) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).2 (by simpa only [m] using hsecond')
        change (d : ZMod m) ^ (n - 1) = -1
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hzero
        exact (add_eq_zero_iff_eq_neg.mp hzero)
      let r := orderOf x
      have hr_d : r ∣ d - 1 := orderOf_dvd_of_pow_eq_one hpow_one
      have hr_twoP : r ∣ 2 * P := by
        apply orderOf_dvd_of_pow_eq_one
        rw [mul_comm 2 P, pow_mul, hpow_neg]
        norm_num
      have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hr_d (by omega)
      have hrle : r ≤ d - 1 := Nat.le_of_dvd (by omega) hr_d
      have hdlt : d < n := by
        rw [← hdk]
        have hdlt' : d < k * d := by
          simpa only [one_mul] using
            (Nat.mul_lt_mul_right hdpos).2 (by omega : 1 < k)
        simpa only [Nat.mul_comm] using hdlt'
      have hrltP : r < P := by dsimp [P]; omega
      have hPnotdivr : ¬ P ∣ r := by
        intro hdiv
        exact (not_le_of_gt hrltP) (Nat.le_of_dvd hrpos hdiv)
      have hcoprime : Nat.Coprime r P :=
        (hPprime.coprime_iff_not_dvd.2 hPnotdivr).symm
      have hr_two : r ∣ 2 := hcoprime.dvd_of_dvd_mul_right hr_twoP
      have hr_not_one : r ≠ 1 := by
        intro hrone
        have hxone : x = 1 := orderOf_eq_one_iff.mp hrone
        have hone_neg : (1 : ZMod m) = -1 := by
          simpa only [hxone, one_pow] using hpow_neg
        let _ : Fact (2 < m) := ⟨hm⟩
        exact ZMod.neg_one_ne_one hone_neg.symm
      have hr_eq_two : r = 2 := by
        have hrle_two := Nat.le_of_dvd (by decide : 0 < 2) hr_two
        omega
      have htwo_dsub : 2 ∣ d - 1 := by simpa only [hr_eq_two] using hr_d
      have hdthree : 3 ≤ d := by
        have := Nat.le_of_dvd (by omega : 0 < d - 1) htwo_dsub
        omega
      have hxsq : x ^ 2 = 1 := by
        have hr_eq_two' : orderOf x = 2 := by simpa only [r] using hr_eq_two
        simpa only [hr_eq_two'] using pow_orderOf_eq_one x
      have hPodd : Odd P := hPprime.odd_of_ne_two (by omega)
      rcases hPodd with ⟨q, hPq⟩
      have hxP : x ^ P = x := by
        rw [hPq, pow_add, pow_mul, hxsq]
        norm_num
      have hdcast : (d : ZMod m) = -1 := by
        change x = -1
        rw [← hxP]
        exact hpow_neg
      have hncast : (n : ZMod m) = 1 := by
        rw [← hdk, Nat.cast_mul, hdcast, hkcast]
        norm_num
      have hPsucc : P + 1 = n := by dsimp [P]; omega
      have hPcast : (P : ZMod m) = 0 := by
        apply add_right_cancel (b := (1 : ZMod m))
        rw [zero_add, ← Nat.cast_one, ← Nat.cast_add, hPsucc]
        exact hncast
      have hmdivP : m ∣ P := (ZMod.natCast_eq_zero_iff _ _).1 hPcast
      have hm_lt_P : m < P := by
        have hkadd : d + k ≤ d * k := Nat.add_le_mul hd hk
        dsimp [m, P]
        rw [← hdk]
        omega
      rcases hPprime.eq_one_or_self_of_dvd m hmdivP with hmone | hmP
      · dsimp [m] at hmone
        omega
      · exact (ne_of_lt hm_lt_P) hmP

/-- OEIS A254748: the average of every twin prime pair has no superdivisor. -/
theorem gerasimov_a254748 :
    ∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) →
      ∀ k : ℕ, 1 ≤ k → k ∣ p + 1 → ¬ IsSuperdivisor (p + 1) k := by
  intro p hp hp2
  have hp_ne_two : p ≠ 2 := by
    intro h
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp2
  have hpodd : Odd p := hp.odd_of_ne_two hp_ne_two
  have hn_even : Even (p + 1) := hpodd.add_one
  have hn : 4 ≤ p + 1 := by
    have := hp.two_le
    omega
  have hpred : p + 1 - 1 = p := by omega
  simpa only [hpred] using
    (no_superdivisor_of_even_and_pred_prime hn hn_even hp)

#print axioms gerasimov_a254748

end D5.S3.Arith.Congruence.GerasimovTwinPrimeMeanNoSuperdivisor
