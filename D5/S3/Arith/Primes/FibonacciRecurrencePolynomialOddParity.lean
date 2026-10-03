/- GID: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddParity
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRecurrencePolynomialOddParity
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd-index recurrence polynomials are even after complexification. -/

import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciRecurrencePolynomialOddParity

open Polynomial
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients

theorem odd_recurrence_polynomial_even (r : ℕ) (z : ℂ) :
    (Polynomial.map (algebraMap ℤ ℂ)
        (fibonacciRecurrencePolynomial (2 * r + 1))).eval (-z) =
      (Polynomial.map (algebraMap ℤ ℂ)
        (fibonacciRecurrencePolynomial (2 * r + 1))).eval z := by
  have hparity (m : ℕ) :
      (Polynomial.map (algebraMap ℤ ℂ)
          (fibonacciRecurrencePolynomial m)).eval (-z) =
        (-1 : ℂ) ^ (m + 1) *
          (Polynomial.map (algebraMap ℤ ℂ)
            (fibonacciRecurrencePolynomial m)).eval z := by
    induction m using Nat.twoStepInduction with
    | zero =>
        simp [fibonacciRecurrencePolynomial]
    | one =>
        simp [fibonacciRecurrencePolynomial]
    | more m ih₀ ih₁ =>
        rw [show m + 2 = (m + 1) + 1 by omega,
          fibonacciRecurrencePolynomial]
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X]
        simp only [eval_add, eval_mul, eval_X, ih₀, ih₁]
        have hp₁ :
            (-1 : ℂ) ^ (m + 3) = -((-1 : ℂ) ^ (m + 2)) := by
          rw [show m + 3 = (m + 2) + 1 by omega, pow_succ]
          ring
        have hp₀ :
            (-1 : ℂ) ^ (m + 1) = (-1 : ℂ) ^ (m + 3) := by
          simp [pow_succ]
        rw [hp₁, hp₀]
        ring
  have h := hparity (2 * r + 1)
  simpa [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul] using h

#print axioms odd_recurrence_polynomial_even

end D5.S3.Arith.Primes.FibonacciRecurrencePolynomialOddParity
