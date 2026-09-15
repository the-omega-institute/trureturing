/- GID: D5/S3/Arith/FibonacciFactorization/LangDyadicSharpness
   generality: G
   mirror-B: none(waiver:unbounded-exact-factorization)
   mirror-E: none(waiver:literal-external-sharpness-refutation)
   anchors: []
   digest: Correct dyadic factors refute the stated A319197 sharpness. -/

import D5.S1.Scale.LucasDoubling
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciFactorization.LangDyadicSharpness

open D5.S1.Scale
open scoped BigOperators

/-- Independent corrected layer recurrence. Index zero corresponds to a(4). -/
def canonicalLayer : ℕ → ℤ
  | 0 => 9
  | k + 1 => 2 * canonicalLayer k ^ 2 - 1

/-- The proposed exact common divisor at external level k+3. -/
def canonicalDivisor (k : ℕ) : ℤ :=
  2 ^ (k + 3) * ∏ j ∈ Finset.range k, canonicalLayer j

/-- The literal no-further-uniform-factor assertion at external level seven,
using only the five entries actually supplied by OEIS, with its offset three. -/
def a319197SeventhSharpness : Prop :=
  ¬∃ c : ℕ, 1 < c ∧ ∀ m : ℕ,
    c * (2 ^ 7 * 1 * 9 * 161 * 51841 * 6989569) ∣ Nat.fib (96 * m)

/-- The exact all-level factorization and its literal A319197 consequence.
The supporting recurrence lives in the proof of the externally stated target. -/
theorem result :
    (∀ k : ℕ, (Nat.fib (6 * 2 ^ k) : ℤ) = canonicalDivisor k ∧
      0 < canonicalDivisor k ∧
      ∀ d : ℤ, (∀ m : ℕ, d ∣ (Nat.fib (6 * 2 ^ k * m) : ℤ)) ↔
        d ∣ canonicalDivisor k) ∧ ¬a319197SeventhSharpness := by
  have hnormal : ∀ k : ℕ,
      (Nat.fib (6 * 2 ^ k) : ℤ) = canonicalDivisor k ∧
      0 < canonicalDivisor k ∧
      ∀ d : ℤ, (∀ m : ℕ, d ∣ (Nat.fib (6 * 2 ^ k * m) : ℤ)) ↔
        d ∣ canonicalDivisor k := by
    intro k
    have hinv : ∀ j : ℕ,
        (Nat.fib (6 * 2 ^ j) : ℤ) = canonicalDivisor j ∧
        goldenLucas (6 * 2 ^ j) = 2 * canonicalLayer j := by
      intro j
      induction j with
      | zero =>
        constructor
        · norm_num [canonicalDivisor, Nat.fib_add_two]
        · simpa [canonicalLayer, Nat.fib_add_two] using
            (golden_lucas_succ_eq_fib_add_fib 5)
      | succ j ih =>
        have hn : 0 < 6 * 2 ^ j :=
          Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
        have hp : 6 * 2 ^ j - 1 + 1 = 6 * 2 ^ j := by omega
        have hp' : 6 * 2 ^ j - 1 + 2 = 6 * 2 ^ j + 1 := by omega
        have hl := golden_lucas_succ_eq_fib_add_fib (6 * 2 ^ j - 1)
        rw [hp, hp'] at hl
        have hi : 6 * 2 ^ (j + 1) = 2 * (6 * 2 ^ j) := by
          rw [pow_succ]
          ring
        have ha : (6 * 2 ^ j - 1) + 6 * 2 ^ j + 1 =
            2 * (6 * 2 ^ j) := by omega
        have hadd := Nat.fib_add (6 * 2 ^ j - 1) (6 * 2 ^ j)
        rw [ha, hp] at hadd
        have hd : (Nat.fib (2 * (6 * 2 ^ j)) : ℤ) =
            (Nat.fib (6 * 2 ^ j) : ℤ) * goldenLucas (6 * 2 ^ j) := by
          calc
            _ = (Nat.fib (6 * 2 ^ j - 1) : ℤ) * (Nat.fib (6 * 2 ^ j) : ℤ) +
                (Nat.fib (6 * 2 ^ j) : ℤ) * (Nat.fib (6 * 2 ^ j + 1) : ℤ) := by
                  exact_mod_cast hadd
            _ = _ := by rw [hl]; ring
        have hs : (-1 : ℤ) ^ (6 * 2 ^ j) = 1 := by
          rw [show 6 * 2 ^ j = 2 * (3 * 2 ^ j) by ring, pow_mul]
          norm_num
        constructor
        · rw [hi, hd, ih.1, ih.2]
          simp only [canonicalDivisor, Finset.prod_range_succ, pow_succ]
          ring
        · rw [hi, golden_lucas_two_mul, ih.2, hs]
          simp only [canonicalLayer]
          ring
    refine ⟨(hinv k).1, ?_, ?_⟩
    · rw [← (hinv k).1]
      have hp : 0 < Nat.fib (6 * 2 ^ k) :=
        Nat.fib_pos.mpr (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) k))
      exact_mod_cast hp
    · intro d
      constructor
      · intro h
        simpa only [Nat.mul_one, (hinv k).1] using h 1
      · intro h m
        have hnat := Nat.fib_dvd (6 * 2 ^ k) (6 * 2 ^ k * m)
          (dvd_mul_right (6 * 2 ^ k) m)
        have hz : (Nat.fib (6 * 2 ^ k) : ℤ) ∣ (Nat.fib (6 * 2 ^ k * m) : ℤ) := by
          exact_mod_cast hnat
        rw [(hinv k).1] at hz
        exact h.trans hz
  refine ⟨hnormal, ?_⟩
  intro hclaim
  apply hclaim
  refine ⟨769, by norm_num, ?_⟩
  intro m
  have hvalue : Nat.fib 96 = 769 * (2 ^ 7 * 1 * 9 * 161 * 51841 * 6989569) := by
    have hz : (Nat.fib 96 : ℤ) =
        ((769 * (2 ^ 7 * 1 * 9 * 161 * 51841 * 6989569) : ℕ) : ℤ) := by
      calc
        _ = canonicalDivisor 4 := by
          simpa only [Nat.reducePow, Nat.reduceMul] using (hnormal 4).1
        _ = _ := by
          norm_num [canonicalDivisor, canonicalLayer, Finset.prod_range_succ]
    exact_mod_cast hz
  rw [← hvalue]
  exact Nat.fib_dvd 96 (96 * m) (dvd_mul_right 96 m)

end D5.S3.Arith.FibonacciFactorization.LangDyadicSharpness
