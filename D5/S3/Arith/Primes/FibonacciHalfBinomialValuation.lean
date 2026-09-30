/- GID: D5/S3/Arith/Primes/FibonacciHalfBinomialValuation
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciHalfBinomialValuation
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Binomial,
     mathlib/module/Mathlib.NumberTheory.Padics.PadicVal.Basic]
   utility: none
   digest: Exact 2-adic valuation of half-binomial coefficients. -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciHalfBinomialValuation

open Polynomial Finset

theorem half_binomial_two_adic_valuation (n : ℕ) :
    padicValRat 2 (Ring.choose (1/2 : ℚ) n) =
      -((n : ℤ) + padicValNat 2 n.factorial) := by
  let oddPart : ℕ → ℤ := fun m =>
    ∏ k ∈ Finset.range m, (1 - 2 * (k : ℤ))
  have half_product (m : ℕ) :
      (2 : ℚ)^m * (m.factorial : ℚ) * Ring.choose (1/2 : ℚ) m =
        (oddPart m : ℚ) := by
    have hchoose :
        (m.factorial : ℚ) * Ring.choose (1/2 : ℚ) m =
          (descPochhammer ℤ m).smeval (1/2 : ℚ) := by
      simpa only [nsmul_eq_mul] using
        (Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℚ) m).symm
    have hprod : ∀ j : ℕ,
        (descPochhammer ℤ j).smeval (1/2 : ℚ) =
          ∏ k ∈ Finset.range j, ((1/2 : ℚ) - k) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [descPochhammer_succ_right, smeval_mul, ih, Finset.prod_range_succ]
          congr 1
          simp only [smeval_sub, smeval_X, smeval_natCast, nsmul_eq_mul,
            pow_zero, mul_one, pow_one]
    rw [mul_assoc, hchoose, hprod]
    have htwo : (2 : ℚ)^m = ∏ _k ∈ Finset.range m, (2 : ℚ) := by simp
    rw [htwo, ← Finset.prod_mul_distrib]
    simp only [oddPart, Int.cast_prod, Int.cast_sub, Int.cast_one, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast]
    apply Finset.prod_congr rfl
    intro k hk
    ring
  have odd_part_not_dvd (m : ℕ) : ¬ (2 : ℤ) ∣ oddPart m := by
    induction m with
    | zero => norm_num [oddPart]
    | succ m ih =>
        change ¬ (2 : ℤ) ∣ ∏ k ∈ Finset.range (m + 1), (1 - 2 * (k : ℤ))
        rw [Finset.prod_range_succ]
        have hfactor : ¬ (2 : ℤ) ∣ (1 - 2 * (m : ℤ)) := by omega
        intro h
        rcases (Int.prime_two.dvd_mul).mp h with h | h
        · exact ih h
        · exact hfactor h
  have hodd := odd_part_not_dvd n
  have hodd_ne : oddPart n ≠ 0 := by
    intro hz
    apply hodd
    rw [hz]
    exact dvd_zero 2
  have hchoose_ne : Ring.choose (1/2 : ℚ) n ≠ 0 := by
    intro hz
    have h := half_product n
    rw [hz, mul_zero] at h
    exact hodd_ne (Int.cast_eq_zero.mp h.symm)
  have hfactorial_ne : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    change padicValRat 2 ((2 : ℕ) : ℚ) = 1
    exact padicValRat.self (by norm_num)
  have hval := congrArg (padicValRat 2) (half_product n)
  rw [padicValRat.mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) hfactorial_ne)
      hchoose_ne,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hfactorial_ne,
    padicValRat.pow, htwo] at hval
  simp only [padicValRat.of_nat, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd hodd] at hval
  omega

#print axioms half_binomial_two_adic_valuation

end D5.S3.Arith.Primes.FibonacciHalfBinomialValuation
