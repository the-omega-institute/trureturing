/- GID: D5/S3/Arith/Primes/GoldenLucasNonsquareThreshold
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenLucasNonsquareThreshold
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd-index Lucas growth crosses the explicit nonsquare threshold. -/

import D5.S1.Scale.Lucas
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold

open D5.S0.Carrier D5.S1.Scale

/-- Lucas numbers at and beyond an odd index of height `2r+1` cross the
integer threshold needed for the large odd Fibonacci-quotient argument. -/
theorem golden_lucas_nonsquare_threshold (r n : ℕ)
    (hr : 119 ≤ r) (hn : 2 * r + 1 ≤ n) :
    128 * (6 : ℤ) ^ r + 4 < goldenLucas n ^ 2 := by
  let A : ℕ → ℤ := fun j => goldenLucas (2 * j + 1)
  have hLucasRec (j : ℕ) :
      goldenLucas (j + 2) = goldenLucas (j + 1) + goldenLucas j := by
    have hp : phi ^ (j + 2) = phi ^ (j + 1) + phi ^ j := by
      rw [pow_add, phi_sq, pow_succ]
      ring
    simp only [goldenLucas, hp, trace]
    simp
    ring
  have hArec (j : ℕ) : A (j + 2) = 3 * A (j + 1) - A j := by
    have h1 := hLucasRec (2 * j + 1)
    have h2 := hLucasRec (2 * j + 2)
    have h3 := hLucasRec (2 * j + 3)
    dsimp [A]
    have heq1 : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
    have heq2 : 2 * (j + 2) + 1 = 2 * j + 5 := by omega
    rw [heq1, heq2]
    have hi1 : 2 * j + 1 + 2 = 2 * j + 3 := by omega
    have hi2 : 2 * j + 2 + 2 = 2 * j + 4 := by omega
    have hi3 : 2 * j + 3 + 2 = 2 * j + 5 := by omega
    have hj1 : 2 * j + 1 + 1 = 2 * j + 2 := by omega
    have hj2 : 2 * j + 2 + 1 = 2 * j + 3 := by omega
    have hj3 : 2 * j + 3 + 1 = 2 * j + 4 := by omega
    rw [hi1, hj1] at h1
    rw [hi2, hj2] at h2
    rw [hi3, hj3] at h3
    omega
  have hA0 : A 0 = 1 := by
    norm_num [A, goldenLucas, trace, phi, pow_succ]
  have hA1 : A 1 = 4 := by
    norm_num [A, goldenLucas, trace, phi, pow_succ]
  have hratio (j : ℕ) : 0 < A j ∧ 5 * A j ≤ 2 * A (j + 1) := by
    induction j with
    | zero => simp [hA0, hA1]
    | succ j ih =>
        obtain ⟨hpos, hstep⟩ := ih
        have hnext : 0 < A (j + 1) := by omega
        have hrec := hArec j
        constructor
        · simpa only [Nat.succ_eq_add_one] using hnext
        · change 5 * A (j + 1) ≤ 2 * A (j + 2)
          omega
  have hgrowth (j : ℕ) : (5 : ℤ) ^ j ≤ (2 : ℤ) ^ j * A j := by
    induction j with
    | zero => simp [hA0]
    | succ j ih =>
        have hmul := mul_le_mul_of_nonneg_left (hratio j).2
          (pow_nonneg (by norm_num : (0 : ℤ) ≤ 2) j)
        calc
          (5 : ℤ) ^ (j + 1) = 5 * 5 ^ j := by ring
          _ ≤ 5 * (2 ^ j * A j) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ ≤ 2 ^ j * (2 * A (j + 1)) := by nlinarith [hmul]
          _ = 2 ^ (j + 1) * A (j + 1) := by ring
  have hbase : (513 : ℤ) * 24 ^ 119 < 4 * 25 ^ 119 := by norm_num
  have hpower (j : ℕ) (hj : 119 ≤ j) :
      (513 : ℤ) * 24 ^ j < 4 * 25 ^ j := by
    induction j, hj using Nat.le_induction with
    | base => exact hbase
    | succ j hj ih =>
        have hp : 0 ≤ (4 : ℤ) * 25 ^ j := by positivity
        calc
          (513 : ℤ) * 24 ^ (j + 1) = 24 * (513 * 24 ^ j) := by ring
          _ < 24 * (4 * 25 ^ j) :=
            mul_lt_mul_of_pos_left ih (by norm_num)
          _ ≤ 25 * (4 * 25 ^ j) := by nlinarith
          _ = 4 * 25 ^ (j + 1) := by ring
  have hsix (j : ℕ) (hj : 119 ≤ j) : (16 : ℤ) < 6 ^ j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
        calc
          (16 : ℤ) < 6 ^ j := ih
          _ ≤ 6 ^ (j + 1) := by
            rw [pow_succ]
            have hp : 0 ≤ (6 : ℤ) ^ j := by positivity
            nlinarith
  have hmargin : (128 : ℤ) * 24 ^ r + 4 * 4 ^ r < 25 ^ r := by
    have h6 := hsix r hr
    have h4pos : 0 < (4 : ℤ) ^ r := by positivity
    have hm := mul_lt_mul_of_pos_left h6 h4pos
    have h24 : (16 : ℤ) * 4 ^ r < 24 ^ r := by
      have heq : (24 : ℤ) ^ r = 4 ^ r * 6 ^ r := by
        rw [show (24 : ℤ) = 4 * 6 by norm_num, mul_pow]
      rw [heq]
      simpa only [mul_comm] using hm
    have hp := hpower r hr
    omega
  have hsq : (25 : ℤ) ^ r ≤ 4 ^ r * A r ^ 2 := by
    have hApos := (hratio r).1
    have hdiff : 0 ≤ (2 : ℤ) ^ r * A r - 5 ^ r := sub_nonneg.mpr (hgrowth r)
    have hsum : 0 ≤ (2 : ℤ) ^ r * A r + 5 ^ r := by positivity
    have hprod := mul_nonneg hdiff hsum
    calc
      (25 : ℤ) ^ r = ((5 : ℤ) ^ r) ^ 2 := by simp [← mul_pow, pow_two]
      _ ≤ ((2 : ℤ) ^ r * A r) ^ 2 := by nlinarith [hprod]
      _ = 4 ^ r * A r ^ 2 := by
        calc
          ((2 : ℤ) ^ r * A r) ^ 2 = ((2 : ℤ) ^ r) ^ 2 * A r ^ 2 := by ring
          _ = 4 ^ r * A r ^ 2 := by
            congr 1
            calc
              ((2 : ℤ) ^ r) ^ 2 = (2 : ℤ) ^ r * 2 ^ r := by ring
              _ = (2 * 2 : ℤ) ^ r := (mul_pow 2 2 r).symm
              _ = (4 : ℤ) ^ r := by norm_num
  have hAr : (128 : ℤ) * 6 ^ r + 4 < A r ^ 2 := by
    have hp4 : 0 < (4 : ℤ) ^ r := by positivity
    have hscaled : 4 ^ r * (128 * 6 ^ r + 4) < 4 ^ r * A r ^ 2 := by
      have h24 : (24 : ℤ) ^ r = 4 ^ r * 6 ^ r := by
        norm_num [← mul_pow]
      rw [h24] at hmargin
      nlinarith [hmargin, hsq]
    by_contra h
    have hle : A r ^ 2 ≤ (128 : ℤ) * 6 ^ r + 4 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hp4)
    exact (not_le_of_gt hscaled) hmul
  have hmono : Monotone (fun k : ℕ => goldenLucas (k + 1)) := by
    intro a b hab
    change goldenLucas (a + 1) ≤ goldenLucas (b + 1)
    rw [golden_lucas_succ_eq_fib_add_fib a,
      golden_lucas_succ_eq_fib_add_fib b]
    have hleft : Nat.fib a ≤ Nat.fib b := Nat.fib_mono hab
    have hright : Nat.fib (a + 2) ≤ Nat.fib (b + 2) :=
      Nat.fib_mono (by omega)
    exact_mod_cast add_le_add hleft hright
  have hLn : A r ≤ goldenLucas n := by
    have heq : n - 1 + 1 = n := by omega
    have hindex : 2 * r ≤ n - 1 := by omega
    simpa only [A, heq] using hmono hindex
  have hApos := (hratio r).1
  have hLnSq : A r ^ 2 ≤ goldenLucas n ^ 2 := by
    have hp : 0 ≤ (goldenLucas n - A r) * (goldenLucas n + A r) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [hp]
  exact lt_of_lt_of_le hAr hLnSq

#print axioms golden_lucas_nonsquare_threshold

end D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold
