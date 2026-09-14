/- GID: D5/S3/Arith/Congruence/FibonacciSquarePlusOneDivisors
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact Fibonacci-divisor indices of Fibonacci square-plus-one values. -/

import Mathlib
import D5.S1.Scale.Fibonacci

namespace D5.S3.Arith.Congruence.FibonacciSquarePlusOneDivisors

private lemma proper_gcd_le_half {k a : ℕ} (hk : 0 < k)
    (hna : ¬ k ∣ a) : Nat.gcd k a ≤ k / 2 := by
  have hne : Nat.gcd k a ≠ k := by
    intro heq
    exact hna (Nat.gcd_eq_left_iff_dvd.mp heq)
  obtain ⟨t, ht⟩ := Nat.gcd_dvd_left k a
  have ht2 : 2 ≤ t := by
    by_contra h
    have hcases : t = 0 ∨ t = 1 := by omega
    rcases hcases with rfl | rfl
    · simp only [Nat.mul_zero] at ht
      omega
    · simp only [Nat.mul_one] at ht
      exact hne ht.symm
  have hh : 2 * Nat.gcd k a ≤ k := by nlinarith
  omega

private lemma fib_half_square_lt {k : ℕ} (hk : 3 ≤ k) :
    Nat.fib (k / 2) ^ 2 < Nat.fib k := by
  by_cases h : k / 2 = 1
  · have heq : k = 3 := by omega
    subst k
    decide
  · let m := k / 2
    have hm : 2 ≤ m := by dsimp [m]; omega
    have hprev : 0 < Nat.fib (m - 1) := Nat.fib_pos.mpr (by omega)
    have hcur : 0 < Nat.fib m := Nat.fib_pos.mpr (by omega)
    have hadd : Nat.fib (2 * m) =
        Nat.fib (m - 1) * Nat.fib m +
          Nat.fib m * Nat.fib (m + 1) := by
      simpa only [show m - 1 + m + 1 = 2 * m by omega,
        show m - 1 + 1 = m by omega] using Nat.fib_add (m - 1) m
    have hprod : Nat.fib m * Nat.fib m ≤
        Nat.fib m * Nat.fib (m + 1) :=
      Nat.mul_le_mul_left _ Nat.fib_le_fib_succ
    have hpos : 0 < Nat.fib (m - 1) * Nat.fib m := Nat.mul_pos hprev hcur
    have hmono : Nat.fib (2 * m) ≤ Nat.fib k :=
      Nat.fib_mono (by dsimp [m]; omega)
    change Nat.fib m ^ 2 < Nat.fib k
    nlinarith

/-- This helper needs no coprimality assumption on the two factors. -/
private lemma fib_two_factor_divisibility {k a b : ℕ} (hk : 3 ≤ k) :
    Nat.fib k ∣ Nat.fib a * Nat.fib b ↔ k ∣ a ∨ k ∣ b := by
  constructor
  · intro hdiv
    by_contra h
    rcases not_or.mp h with ⟨ha, hb⟩
    have hsmallA := proper_gcd_le_half (by omega : 0 < k) ha
    have hsmallB := proper_gcd_le_half (by omega : 0 < k) hb
    have hdiv' : Nat.fib k ∣
        Nat.fib (Nat.gcd k a) * Nat.fib (Nat.gcd k b) := by
      simpa only [Nat.fib_gcd] using
        (Nat.dvd_gcd_mul_gcd_iff_dvd_mul
          (k := Nat.fib k) (n := Nat.fib a) (m := Nat.fib b)).mpr hdiv
    have hp : 0 < Nat.fib (Nat.gcd k a) * Nat.fib (Nat.gcd k b) := by
      apply Nat.mul_pos
      · exact Nat.fib_pos.mpr (Nat.gcd_pos_of_pos_left a (by omega))
      · exact Nat.fib_pos.mpr (Nat.gcd_pos_of_pos_left b (by omega))
    have hle := Nat.le_of_dvd hp hdiv'
    have hbound : Nat.fib (Nat.gcd k a) * Nat.fib (Nat.gcd k b) ≤
        Nat.fib (k / 2) ^ 2 := by
      simpa only [pow_two] using
        Nat.mul_le_mul (Nat.fib_mono hsmallA) (Nat.fib_mono hsmallB)
    have hlt := fib_half_square_lt hk
    omega
  · rintro (ha | hb)
    · exact dvd_mul_of_dvd_left (Nat.fib_dvd k a ha) (Nat.fib b)
    · exact dvd_mul_of_dvd_right (Nat.fib_dvd k b hb) (Nat.fib a)

/-- For every even index at least two, these are exactly the non-unit
Fibonacci divisor indices of its square-plus-one value. -/
theorem even_square_plus_one_divisors (m k : ℕ) (hk : 3 ≤ k) :
    Nat.fib k ∣ Nat.fib (2 * m + 2) ^ 2 + 1 ↔
      k ∣ 2 * m + 1 ∨ k ∣ 2 * m + 3 := by
  have hc := D5.S1.Scale.fib_cassini_from_golden_norm (2 * m + 1)
  simp only [show 2 * m + 1 + 2 = 2 * m + 3 by omega,
    show 2 * m + 1 + 1 = 2 * m + 2 by omega] at hc
  norm_num [pow_add, pow_mul] at hc
  have hz : (Nat.fib (2 * m + 1) : ℤ) * Nat.fib (2 * m + 3) =
      (Nat.fib (2 * m + 2) : ℤ) ^ 2 + 1 := by nlinarith
  have hn : Nat.fib (2 * m + 1) * Nat.fib (2 * m + 3) =
      Nat.fib (2 * m + 2) ^ 2 + 1 := by exact_mod_cast hz
  rw [← hn]
  exact fib_two_factor_divisibility hk

/-- For every odd index at least three, the two relevant indices are
separated from the centre by two. -/
theorem odd_square_plus_one_divisors (m k : ℕ) (hk : 3 ≤ k) :
    Nat.fib k ∣ Nat.fib (2 * m + 3) ^ 2 + 1 ↔
      k ∣ 2 * m + 1 ∨ k ∣ 2 * m + 5 := by
  have h3 : Nat.fib (2 * m + 3) =
      Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := by
    simpa only [show 2 * m + 1 + 2 = 2 * m + 3 by omega,
      show 2 * m + 1 + 1 = 2 * m + 2 by omega] using
      (Nat.fib_add_two (n := 2 * m + 1))
  have h4 : Nat.fib (2 * m + 4) =
      Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := by
    simpa only [show 2 * m + 2 + 2 = 2 * m + 4 by omega,
      show 2 * m + 2 + 1 = 2 * m + 3 by omega] using
      (Nat.fib_add_two (n := 2 * m + 2))
  have h5 : Nat.fib (2 * m + 5) =
      Nat.fib (2 * m + 3) + Nat.fib (2 * m + 4) := by
    simpa only [show 2 * m + 3 + 2 = 2 * m + 5 by omega,
      show 2 * m + 3 + 1 = 2 * m + 4 by omega] using
      (Nat.fib_add_two (n := 2 * m + 3))
  have hc := D5.S1.Scale.fib_cassini_from_golden_norm (2 * m + 2)
  simp only [show 2 * m + 2 + 2 = 2 * m + 4 by omega,
    show 2 * m + 2 + 1 = 2 * m + 3 by omega] at hc
  norm_num [pow_add, pow_mul] at hc
  simp only [h4, h3, Nat.cast_add] at hc
  have hz : (Nat.fib (2 * m + 1) : ℤ) * Nat.fib (2 * m + 5) =
      (Nat.fib (2 * m + 3) : ℤ) ^ 2 + 1 := by
    simp only [h5, h4, h3, Nat.cast_add]
    nlinarith [hc]
  have hn : Nat.fib (2 * m + 1) * Nat.fib (2 * m + 5) =
      Nat.fib (2 * m + 3) ^ 2 + 1 := by exact_mod_cast hz
  rw [← hn]
  exact fib_two_factor_divisibility hk

end D5.S3.Arith.Congruence.FibonacciSquarePlusOneDivisors
