/- GID: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialChebyshev
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRecurrencePolynomialChebyshev
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Chebyshev]
   utility: none
   digest: Complex Chebyshev representation of the plus-recurrence polynomial. -/

import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
import Mathlib.RingTheory.Polynomial.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciRecurrencePolynomialChebyshev

open Polynomial
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients

private noncomputable def chebyshevBridge (k : ℕ) : ℂ[X] :=
  C ((-Complex.I) ^ k) *
    (Polynomial.Chebyshev.U ℂ (k : ℤ)).comp (C (Complex.I / 2) * X)

private noncomputable def chebyshevSBridge (k : ℕ) : ℂ[X] :=
  C ((-Complex.I) ^ k) *
    (Polynomial.Chebyshev.S ℂ (k : ℤ)).comp (C Complex.I * X)

theorem fibonacci_recurrence_polynomial_chebyshev (k : ℕ) :
    Polynomial.map (algebraMap ℤ ℂ)
        (fibonacciRecurrencePolynomial (k + 1)) =
      chebyshevBridge k := by
  have hS (k : ℕ) :
      Polynomial.map (algebraMap ℤ ℂ)
          (fibonacciRecurrencePolynomial (k + 1)) =
        chebyshevSBridge k := by
    induction k using Nat.twoStepInduction with
    | zero =>
        simp [chebyshevSBridge, fibonacciRecurrencePolynomial]
    | one =>
        simp [chebyshevSBridge, fibonacciRecurrencePolynomial,
          Complex.I_mul_I]
        rw [← mul_assoc, ← map_mul, Complex.I_mul_I]
        simp
    | more k ih₀ ih₁ =>
        have hs := Polynomial.Chebyshev.S_add_two ℂ (k : ℤ)
        rw [show k + 2 + 1 = (k + 1) + 2 by omega,
          fibonacciRecurrencePolynomial]
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X]
        rw [ih₁, ih₀]
        simp only [chebyshevSBridge]
        rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by norm_num, hs]
        simp only [sub_comp, mul_comp, X_comp]
        rw [show (-Complex.I) ^ (k + 1) = (-Complex.I) ^ k * (-Complex.I) by
          rw [pow_succ]]
        have hnegI : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
          simp [Complex.I_mul_I]
        rw [show (-Complex.I) ^ (k + 2) = -((-Complex.I) ^ k) by
          rw [show k + 2 = k + 1 + 1 by omega, pow_succ, pow_succ]
          calc
            (-Complex.I) ^ k * -Complex.I * -Complex.I =
                (-Complex.I) ^ k * ((-Complex.I) * (-Complex.I)) := by ring
            _ = (-Complex.I) ^ k * (-1) := by rw [hnegI]
            _ = -((-Complex.I) ^ k) := by ring]
        simp only [map_mul, map_neg]
        norm_num
        ring
  rw [hS k]
  simp only [chebyshevSBridge, chebyshevBridge]
  rw [Polynomial.Chebyshev.S_eq_U_comp_half_mul_X]
  simp only [comp_assoc]
  have harg :
      (C (⅟(2 : ℂ)) * X).comp (C Complex.I * X) =
        C (Complex.I / 2) * X := by
    simp only [mul_comp, C_comp, X_comp]
    calc
      C (⅟(2 : ℂ)) * (C Complex.I * X) =
          C (⅟(2 : ℂ)) * C Complex.I * X := by ring
      _ = C (Complex.I * ⅟(2 : ℂ)) * X := by
        rw [C_mul]
        congr 1
        ring
      _ = C (Complex.I / 2) * X := by
        congr 1
  rw [harg]

#print axioms fibonacci_recurrence_polynomial_chebyshev

end D5.S3.Arith.Primes.FibonacciRecurrencePolynomialChebyshev
