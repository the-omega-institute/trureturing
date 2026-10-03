/- GID: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddBridge
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRecurrencePolynomialOddBridge
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd-index recurrence bridge for Fibonacci quotients. -/

import D5.S1.Scale.Lucas
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciRecurrencePolynomialOddBridge

open Polynomial
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients

theorem odd_fibonacci_recurrence_bridge (n m : ℕ) (hn : Odd n) :
    (Nat.fib n : ℤ) *
        (fibonacciRecurrencePolynomial m).eval (goldenLucas n) =
      (Nat.fib (m * n) : ℤ) ∧
    (Nat.fib (m * n) : ℚ) / (Nat.fib n : ℚ) =
      (((fibonacciRecurrencePolynomial m).eval (goldenLucas n) : ℤ) : ℚ) := by
  let z : GoldenInt := phi ^ n
  have hnorm : norm z = -1 := by
    dsimp [z]
    rw [norm_phi_pow, hn.neg_one_pow]
  have htrace : trace z = goldenLucas n := by
    rfl
  have hquad : z ^ 2 = (trace z : GoldenInt) * z + 1 := by
    have hgeneral : ∀ w : GoldenInt,
        w ^ 2 = (trace w : GoldenInt) * w -
          (D5.S0.Carrier.norm w : GoldenInt) := by
      intro w
      apply GoldenInt.ext
      · simp only [pow_two, a_mul, sub_eq_add_neg, a_add, a_neg,
          a_intCast, b_intCast, trace,
          D5.S0.Carrier.norm]
        ring
      · simp only [pow_two, b_mul, sub_eq_add_neg, b_add, b_neg,
          a_intCast, b_intCast, trace,
          D5.S0.Carrier.norm]
        ring
    have h := hgeneral z
    rw [hnorm] at h
    norm_num at h ⊢
    exact h
  have hpower_rec (k : ℕ) :
      (z ^ (k + 2)).b = trace z * (z ^ (k + 1)).b + (z ^ k).b := by
    have hpoweq : z ^ (k + 2) =
        (trace z : GoldenInt) * z ^ (k + 1) + z ^ k := by
      calc
        z ^ (k + 2) = z ^ k * z ^ 2 := by rw [pow_add]
        _ = z ^ k * ((trace z : GoldenInt) * z + 1) := by rw [hquad]
        _ = (trace z : GoldenInt) * z ^ (k + 1) + z ^ k := by
          calc
            z ^ k * ((trace z : GoldenInt) * z + 1) =
                (z ^ k * (trace z : GoldenInt)) * z + z ^ k := by
              rw [mul_add, mul_one, ← mul_assoc]
            _ = (trace z : GoldenInt) * (z ^ k * z) + z ^ k := by
              ring
            _ = (trace z : GoldenInt) * z ^ (k + 1) + z ^ k := by
              rw [pow_succ]
    have hb := congrArg GoldenInt.b hpoweq
    simpa [b_mul] using hb
  have hmain (k : ℕ) :
      z.b * (fibonacciRecurrencePolynomial k).eval (trace z) =
        (z ^ k).b := by
    induction k using Nat.twoStepInduction with
    | zero =>
        simp [fibonacciRecurrencePolynomial]
    | one =>
        simp [fibonacciRecurrencePolynomial]
    | more k ih₀ ih₁ =>
        calc
          z.b * (fibonacciRecurrencePolynomial (k + 2)).eval (trace z) =
              z.b *
                (trace z *
                    (fibonacciRecurrencePolynomial (k + 1)).eval (trace z) +
                  (fibonacciRecurrencePolynomial k).eval (trace z)) := by
            simp [fibonacciRecurrencePolynomial, eval_add, eval_mul, eval_X]
          _ = trace z * (z ^ (k + 1)).b + (z ^ k).b := by
            calc
              z.b *
                    (trace z *
                        (fibonacciRecurrencePolynomial (k + 1)).eval
                          (trace z) +
                      (fibonacciRecurrencePolynomial k).eval (trace z)) =
                  trace z *
                      (z.b *
                        (fibonacciRecurrencePolynomial (k + 1)).eval
                          (trace z)) +
                    z.b * (fibonacciRecurrencePolynomial k).eval (trace z) := by
                ring
              _ = trace z * (z ^ (k + 1)).b + (z ^ k).b := by
                rw [ih₁, ih₀]
          _ = (z ^ (k + 2)).b := (hpower_rec k).symm
  have hzcoord : z.b = (Nat.fib n : ℤ) := by
    dsimp [z]
    exact golden_phi_pow_b_eq_fib_index n
  have hzpow (k : ℕ) : z ^ k = phi ^ (n * k) := by
    dsimp [z]
    rw [pow_mul]
  have hzpowcoord (k : ℕ) : (z ^ k).b = (Nat.fib (n * k) : ℤ) := by
    rw [hzpow]
    exact golden_phi_pow_b_eq_fib_index (n * k)
  have hprod :
      (Nat.fib n : ℤ) *
          (fibonacciRecurrencePolynomial m).eval (goldenLucas n) =
        (Nat.fib (m * n) : ℤ) := by
    rw [← htrace, ← hzcoord, hmain m, hzpowcoord]
    simp [Nat.mul_comm]
  refine ⟨hprod, ?_⟩
  have hnpos : 0 < n := by
    rcases hn with ⟨k, hk⟩
    omega
  have hfibpos : 0 < Nat.fib n := Nat.fib_pos.mpr hnpos
  have hfibne : (Nat.fib n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hfibpos)
  apply (div_eq_iff hfibne).2
  have hprodQ :
      (Nat.fib n : ℚ) *
          (((fibonacciRecurrencePolynomial m).eval (goldenLucas n) : ℤ) : ℚ) =
        (Nat.fib (m * n) : ℚ) := by
    exact_mod_cast hprod
  calc
    (Nat.fib (m * n) : ℚ) =
        (Nat.fib n : ℚ) *
          (((fibonacciRecurrencePolynomial m).eval (goldenLucas n) : ℤ) : ℚ) :=
      hprodQ.symm
    _ = (((fibonacciRecurrencePolynomial m).eval (goldenLucas n) : ℤ) : ℚ) *
        (Nat.fib n : ℚ) := by ring

#print axioms odd_fibonacci_recurrence_bridge

end D5.S3.Arith.Primes.FibonacciRecurrencePolynomialOddBridge
