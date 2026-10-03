/- GID: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Near-leading coefficients of the Fibonacci recurrence polynomial. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients

open Polynomial

/-- The polynomial sequence with initial values `0, 1` and Fibonacci
recurrence. Its index is the index used in the theory volume. -/
noncomputable def fibonacciRecurrencePolynomial : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => X * fibonacciRecurrencePolynomial (n + 1) +
      fibonacciRecurrencePolynomial n

/-- The Fibonacci recurrence polynomial has its expected degree and monic
leading term. The coefficient two degrees lower grows by one at each step,
and is odd at every odd index greater than one. -/
theorem fibonacci_recurrence_polynomial_coefficients :
    (∀ n : ℕ, (fibonacciRecurrencePolynomial (n + 1)).natDegree = n ∧
      (fibonacciRecurrencePolynomial (n + 1)).coeff n = 1) ∧
    (∀ n : ℕ, (fibonacciRecurrencePolynomial (n + 3)).coeff n = (n + 1 : ℤ)) ∧
    (∀ r : ℕ, 1 ≤ r →
      (fibonacciRecurrencePolynomial (2 * r + 1)).coeff (2 * r - 2) =
        (2 * r - 1 : ℤ) ∧ Odd (2 * r - 1)) := by
  have hdegree (n : ℕ) :
      (fibonacciRecurrencePolynomial (n + 1)).natDegree = n := by
    induction n using Nat.twoStepInduction with
    | zero => simp [fibonacciRecurrencePolynomial]
    | one => simp [fibonacciRecurrencePolynomial]
    | more n ih₀ ih₁ =>
        have hne : fibonacciRecurrencePolynomial (n + 2) ≠ 0 := by
          intro hz
          rw [hz, natDegree_zero] at ih₁
          omega
        have hleft :
            (X * fibonacciRecurrencePolynomial (n + 2)).natDegree = n + 2 := by
          rw [natDegree_X_mul hne, ih₁]
        have hright :
            (fibonacciRecurrencePolynomial (n + 1)).natDegree <
              (X * fibonacciRecurrencePolynomial (n + 2)).natDegree := by
          rw [hleft, ih₀]
          omega
        rw [show n + 2 + 1 = (n + 1) + 2 by omega,
          fibonacciRecurrencePolynomial]
        rw [natDegree_add_eq_left_of_natDegree_lt hright, hleft]
  have hleading (n : ℕ) :
      (fibonacciRecurrencePolynomial (n + 1)).coeff n = 1 := by
    induction n using Nat.twoStepInduction with
    | zero => simp [fibonacciRecurrencePolynomial]
    | one => simp [fibonacciRecurrencePolynomial]
    | more n ih₀ ih₁ =>
        have hzero :
            (fibonacciRecurrencePolynomial (n + 1)).coeff (n + 2) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hdegree]
          omega
        rw [show n + 2 + 1 = (n + 1) + 2 by omega,
          fibonacciRecurrencePolynomial, coeff_add, coeff_X_mul]
        rw [ih₁, hzero]
        simp
  have hsecond (n : ℕ) :
      (fibonacciRecurrencePolynomial (n + 3)).coeff n = (n + 1 : ℤ) := by
    induction n with
    | zero => simp [fibonacciRecurrencePolynomial]
    | succ n ih =>
        have hlead := hleading (n + 1)
        rw [show n + 1 + 3 = (n + 2) + 2 by omega,
          fibonacciRecurrencePolynomial, coeff_add, coeff_X_mul]
        rw [ih, hlead]
        push_cast
        ring
  refine ⟨fun n => ⟨hdegree n, hleading n⟩, hsecond, ?_⟩
  intro r hr
  have h := hsecond (2 * r - 2)
  have heq : 2 * r - 2 + 3 = 2 * r + 1 := by omega
  rw [heq] at h
  constructor
  · calc
      (fibonacciRecurrencePolynomial (2 * r + 1)).coeff (2 * r - 2) =
          ((2 * r - 2 : ℕ) + 1 : ℤ) := h
      _ = (2 * r - 1 : ℤ) := by omega
  · refine ⟨r - 1, ?_⟩
    omega

#print axioms fibonacci_recurrence_polynomial_coefficients

end D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
