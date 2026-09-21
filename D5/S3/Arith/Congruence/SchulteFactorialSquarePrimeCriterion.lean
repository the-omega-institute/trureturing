/- GID: D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Schulte's factorial-square sequence satisfies his prime divisibility criterion. -/

import D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue
import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Nat

namespace D5.S3.Arith.Congruence.SchulteFactorialSquarePrimeCriterion

/-- OEIS A006472: `m! * (m - 1)! / 2 ^ (m - 1)`, with exact natural division. -/
def a (m : ℕ) : ℕ := (m.factorial * (m - 1).factorial) / 2 ^ (m - 1)

private theorem composite_dvd_a {n : ℕ} (hn : 9 ≤ n) (hnprime : ¬n.Prime) :
    n ∣ a (n - 1) := by
  have exact_dvd (m : ℕ) (_hm : 1 ≤ m) :
      2 ^ (m - 1) ∣ m.factorial * (m - 1).factorial := by
    have hpow (k : ℕ) : 2 ^ k ∣ (2 * k).factorial := by
      cases k with
      | zero => norm_num
      | succ k =>
        have hfac : (2 * (k + 1)).factorial =
            (2 * (k + 1))‼ * (2 * (k + 1) - 1)‼ := by
          calc
            (2 * (k + 1)).factorial = ((2 * (k + 1) - 1) + 1).factorial := by
              congr 1
            _ = ((2 * (k + 1) - 1) + 1)‼ * (2 * (k + 1) - 1)‼ :=
              Nat.factorial_eq_mul_doubleFactorial (2 * (k + 1) - 1)
            _ = (2 * (k + 1))‼ * (2 * (k + 1) - 1)‼ := by
              rw [show 2 * (k + 1) - 1 + 1 = 2 * (k + 1) by omega]
        rw [hfac, Nat.doubleFactorial_two_mul]
        exact dvd_mul_of_dvd_left (dvd_mul_right (2 ^ (k + 1)) (k + 1).factorial) _
    have hhalf (x : ℕ) : 2 ^ (x / 2) ∣ x.factorial :=
      (hpow (x / 2)).trans (Nat.factorial_dvd_factorial (Nat.mul_div_le x 2))
    have hsum : m / 2 + (m - 1) / 2 = m - 1 := by omega
    have hpow_eq : 2 ^ (m - 1) = 2 ^ (m / 2) * 2 ^ ((m - 1) / 2) := by
      rw [← pow_add, hsum]
    rw [hpow_eq]
    exact Nat.mul_dvd_mul (hhalf m) (hhalf (m - 1))
  have exact_mul (m : ℕ) (hm : 1 ≤ m) :
      2 ^ (m - 1) * a m = m.factorial * (m - 1).factorial := by
    apply Nat.mul_div_cancel'
    exact exact_dvd m hm
  have a_even_formula (k : ℕ) (hk : 1 ≤ k) :
      a (2 * k - 1) =
        (k - 1).factorial * (k - 1).factorial *
          (2 * k - 1)‼ * (2 * k - 3)‼ := by
    by_cases hk1 : k = 1
    · subst k
      norm_num [a]
    have hk2 : 2 ≤ k := by omega
    have hm : 1 ≤ 2 * k - 1 := by omega
    have hf1 : (2 * k - 1).factorial = (2 * k - 1)‼ * (2 * k - 2)‼ := by
      calc
        (2 * k - 1).factorial = ((2 * k - 2) + 1).factorial := by
          congr 1
          omega
        _ = ((2 * k - 2) + 1)‼ * (2 * k - 2)‼ :=
          Nat.factorial_eq_mul_doubleFactorial (2 * k - 2)
        _ = (2 * k - 1)‼ * (2 * k - 2)‼ := by
          rw [show 2 * k - 2 + 1 = 2 * k - 1 by omega]
    have hf2 : (2 * k - 2).factorial = (2 * k - 2)‼ * (2 * k - 3)‼ := by
      calc
        (2 * k - 2).factorial = ((2 * k - 3) + 1).factorial := by
          congr 1
          omega
        _ = ((2 * k - 3) + 1)‼ * (2 * k - 3)‼ :=
          Nat.factorial_eq_mul_doubleFactorial (2 * k - 3)
        _ = (2 * k - 2)‼ * (2 * k - 3)‼ := by
          rw [show 2 * k - 3 + 1 = 2 * k - 2 by omega]
    have hdf : (2 * k - 2)‼ = 2 ^ (k - 1) * (k - 1).factorial := by
      rw [show 2 * k - 2 = 2 * (k - 1) by omega, Nat.doubleFactorial_two_mul]
    have hpow : 2 ^ (2 * k - 1 - 1) = 2 ^ (k - 1) * 2 ^ (k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hleft := exact_mul (2 * k - 1) hm
    have hright :
        2 ^ (2 * k - 1 - 1) *
            ((k - 1).factorial * (k - 1).factorial *
              (2 * k - 1)‼ * (2 * k - 3)‼) =
          (2 * k - 1).factorial * (2 * k - 1 - 1).factorial := by
      rw [hpow, hf1, show 2 * k - 1 - 1 = 2 * k - 2 by omega, hf2, hdf]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (hleft.trans hright.symm)
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · obtain ⟨k, hk⟩ := hn_even
    have hn_eq : n = 2 * k := by omega
    have hk5 : 5 ≤ k := by omega
    rw [hn_eq]
    have haformula := a_even_formula k (by omega)
    rcases Nat.even_or_odd k with hk_even | hk_odd
    · have hkfac : k ∣ (k - 1).factorial := by
        obtain ⟨r, hr⟩ := hk_even
        rw [hr]
        have hr3 : 3 ≤ r := by omega
        have hbase : 2 * r ∣ (2 : ℕ).factorial * r.factorial :=
          Nat.mul_dvd_mul (by norm_num) (Nat.dvd_factorial (by omega) le_rfl)
        have hcombine : (2 : ℕ).factorial * r.factorial ∣ (2 + r).factorial :=
          Nat.factorial_mul_factorial_dvd_factorial_add 2 r
        have hlift : (2 + r).factorial ∣ (r + r - 1).factorial :=
          Nat.factorial_dvd_factorial (by omega)
        simpa [two_mul] using hbase.trans (hcombine.trans hlift)
      have htwofac : 2 ∣ (k - 1).factorial :=
        Nat.dvd_factorial (by norm_num) (by omega)
      have hmain : 2 * k ∣ (k - 1).factorial * (k - 1).factorial :=
        Nat.mul_dvd_mul htwofac hkfac
      rw [haformula]
      simpa [mul_assoc] using
        dvd_mul_of_dvd_left hmain ((2 * k - 1)‼ * (2 * k - 3)‼)
    · have hkcop2 : k.Coprime 2 := hk_odd.coprime_two_right
      have hm : 1 ≤ 2 * k - 1 := by omega
      have hmul := exact_mul (2 * k - 1) hm
      have hkprod : k ∣ (2 * k - 1).factorial * (2 * k - 2).factorial :=
        dvd_mul_of_dvd_right (Nat.dvd_factorial (by omega) (by omega)) _
      have hkpow : k.Coprime (2 ^ (2 * k - 2)) := hkcop2.pow_right _
      have hka : k ∣ a (2 * k - 1) := by
        apply hkpow.dvd_mul_left.mp
        rw [show 2 ^ (2 * k - 2) * a (2 * k - 1) =
          (2 * k - 1).factorial * (2 * k - 2).factorial by
            simpa only [show 2 * k - 1 - 1 = 2 * k - 2 by omega] using hmul]
        exact hkprod
      have htwofac : 2 ∣ (k - 1).factorial :=
        Nat.dvd_factorial (by norm_num) (by omega)
      have htwoa : 2 ∣ a (2 * k - 1) := by
        rw [haformula]
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left htwofac (k - 1).factorial) (2 * k - 1)‼)
          (2 * k - 3)‼
      simpa [mul_comm] using hkcop2.mul_dvd_of_dvd_of_dvd hka htwoa
  · have heven : Even (n - 1) := hn_odd.tsub_odd odd_one
    have htri : (n - 1) * ((n - 1) + 1) / 2 ∣ (n - 1).factorial :=
      D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime
          (by omega) (by
            intro h
            have hp : Nat.Prime n := by
              simpa only [show n - 1 + 1 = n by omega] using h.1
            exact hnprime hp)
    have hntri : n ∣ (n - 1) * ((n - 1) + 1) / 2 := by
      rw [show n - 1 + 1 = n by omega, mul_comm,
        Nat.mul_div_assoc n heven.two_dvd]
      exact dvd_mul_right n ((n - 1) / 2)
    have hnfac : n ∣ (n - 1).factorial := hntri.trans htri
    have hnprod : n ∣ (n - 1).factorial * (n - 2).factorial :=
      dvd_mul_of_dvd_left hnfac _
    have hmul := exact_mul (n - 1) (by omega)
    have hcop : n.Coprime (2 ^ (n - 2)) := hn_odd.coprime_two_right.pow_right _
    apply hcop.dvd_mul_left.mp
    rw [show 2 ^ (n - 2) * a (n - 1) =
      (n - 1).factorial * (n - 2).factorial by
        simpa only [show n - 1 - 1 = n - 2 by omega] using hmul]
    exact hnprod

/-- Schulte's criterion: `n` divides `2 * A006472(n - 1) + 4` exactly when `n` is prime. -/
theorem result (n : ℕ) (hn : 2 ≤ n) : n ∣ 2 * a (n - 1) + 4 ↔ n.Prime := by
  have exact_dvd (m : ℕ) (_hm : 1 ≤ m) :
      2 ^ (m - 1) ∣ m.factorial * (m - 1).factorial := by
    have hpow (k : ℕ) : 2 ^ k ∣ (2 * k).factorial := by
      cases k with
      | zero => norm_num
      | succ k =>
        have hfac : (2 * (k + 1)).factorial =
            (2 * (k + 1))‼ * (2 * (k + 1) - 1)‼ := by
          calc
            (2 * (k + 1)).factorial = ((2 * (k + 1) - 1) + 1).factorial := by
              congr 1
            _ = ((2 * (k + 1) - 1) + 1)‼ * (2 * (k + 1) - 1)‼ :=
              Nat.factorial_eq_mul_doubleFactorial (2 * (k + 1) - 1)
            _ = (2 * (k + 1))‼ * (2 * (k + 1) - 1)‼ := by
              rw [show 2 * (k + 1) - 1 + 1 = 2 * (k + 1) by omega]
        rw [hfac, Nat.doubleFactorial_two_mul]
        exact dvd_mul_of_dvd_left (dvd_mul_right (2 ^ (k + 1)) (k + 1).factorial) _
    have hhalf (x : ℕ) : 2 ^ (x / 2) ∣ x.factorial :=
      (hpow (x / 2)).trans (Nat.factorial_dvd_factorial (Nat.mul_div_le x 2))
    have hsum : m / 2 + (m - 1) / 2 = m - 1 := by omega
    have hpow_eq : 2 ^ (m - 1) = 2 ^ (m / 2) * 2 ^ ((m - 1) / 2) := by
      rw [← pow_add, hsum]
    rw [hpow_eq]
    exact Nat.mul_dvd_mul (hhalf m) (hhalf (m - 1))
  have exact_mul (m : ℕ) (hm : 1 ≤ m) :
      2 ^ (m - 1) * a m = m.factorial * (m - 1).factorial := by
    apply Nat.mul_div_cancel'
    exact exact_dvd m hm
  constructor
  · intro hdiv
    by_contra hnprime
    by_cases hn9 : 9 ≤ n
    · have hna : n ∣ a (n - 1) := composite_dvd_a hn9 hnprime
      have htwoa : n ∣ 2 * a (n - 1) := dvd_mul_of_dvd_right hna 2
      have hfour : n ∣ 4 := ((Nat.dvd_add_iff_right htwoa).symm).mp hdiv
      have hn4 : n ≤ 4 := Nat.le_of_dvd (by norm_num) hfour
      omega
    · interval_cases n <;> norm_num [a, Nat.factorial] at hdiv
      all_goals exact hnprime (by decide)
  · intro hp
    by_cases hn2 : n = 2
    · subst n
      norm_num [a]
    have hn3 : 3 ≤ n := by omega
    have hnodd : Odd n := hp.odd_of_ne_two hn2
    let _ : Fact (Nat.Prime n) := ⟨hp⟩
    have hmul := exact_mul (n - 1) (by omega)
    have hmul_norm :
        2 ^ (n - 2) * a (n - 1) =
          (n - 1).factorial * (n - 2).factorial := by
      simpa only [show n - 1 - 1 = n - 2 by omega] using hmul
    have hscale :
        2 ^ (n - 2) * (2 * a (n - 1) + 4) =
          2 * (n - 1).factorial * (n - 2).factorial + 2 ^ n := by
      have hpow : 4 * 2 ^ (n - 2) = 2 ^ n := by
        calc
          4 * 2 ^ (n - 2) = 2 ^ 2 * 2 ^ (n - 2) := by norm_num
          _ = 2 ^ (2 + (n - 2)) := by rw [pow_add]
          _ = 2 ^ n := by
            congr 1
            omega
      calc
        _ = 2 * (2 ^ (n - 2) * a (n - 1)) + 4 * 2 ^ (n - 2) := by ring
        _ = _ := by rw [hmul_norm, hpow]; ring
    have hw : (((n - 1).factorial : ℕ) : ZMod n) = -1 := by
      exact ZMod.wilsons_lemma n
    have hnminus : ((n - 1 : ℕ) : ZMod n) = -1 := by
      calc
        ((n - 1 : ℕ) : ZMod n) = (n : ZMod n) - 1 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        _ = -1 := by rw [ZMod.natCast_self]; simp
    have hfac2 : (((n - 2).factorial : ℕ) : ZMod n) = 1 := by
      have hfacrec :
          (((n - 1).factorial : ℕ) : ZMod n) =
            ((n - 1 : ℕ) : ZMod n) * (((n - 2).factorial : ℕ) : ZMod n) := by
        rw [show n - 1 = (n - 2) + 1 by omega, Nat.factorial_succ]
        simp
      have hrel :
          (-1 : ZMod n) * (((n - 2).factorial : ℕ) : ZMod n) = -1 := by
        calc
          _ = ((n - 1 : ℕ) : ZMod n) * (((n - 2).factorial : ℕ) : ZMod n) := by
            rw [hnminus]
          _ = (((n - 1).factorial : ℕ) : ZMod n) := hfacrec.symm
          _ = -1 := hw
      simpa only [neg_mul, one_mul, neg_inj] using hrel
    have htwo_ne : (2 : ZMod n) ≠ 0 := by
      intro hzero
      have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp hzero
      have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hfermat : (2 : ZMod n) ^ (n - 1) = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one htwo_ne
    have htwo_pow : (((2 ^ n : ℕ) : ZMod n)) = 2 := by
      calc
        (((2 ^ n : ℕ) : ZMod n)) = (2 : ZMod n) ^ n := by simp
        _ = (2 : ZMod n) ^ (n - 1 + 1) := by
          congr 1
          omega
        _ = (2 : ZMod n) ^ (n - 1) * 2 := by rw [pow_succ]
        _ = 2 := by rw [hfermat, one_mul]
    have hscaled : n ∣ 2 ^ (n - 2) * (2 * a (n - 1) + 4) := by
      rw [hscale, ← ZMod.natCast_eq_zero_iff]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hw, hfac2, htwo_pow]
      ring
    have hcop : n.Coprime (2 ^ (n - 2)) := hnodd.coprime_two_right.pow_right _
    exact hcop.dvd_mul_left.mp hscaled

end D5.S3.Arith.Congruence.SchulteFactorialSquarePrimeCriterion
