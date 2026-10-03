/- GID: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialThirdCoefficient
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRecurrencePolynomialThirdCoefficient
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Third near-leading coefficient of the Fibonacci recurrence polynomial. -/

import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient

open Polynomial
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients

/-- The coefficient two layers below the second layer is a binomial
coefficient.  It is the next nonzero coefficient input for the square-root
series attached to an odd recurrence polynomial. -/
theorem fibonacci_recurrence_polynomial_third_coefficient :
    ∀ n : ℕ,
      (fibonacciRecurrencePolynomial (n + 5)).coeff n =
        (Nat.choose (n + 2) 2 : ℤ) := by
  intro n
  induction n with
  | zero =>
      norm_num [fibonacciRecurrencePolynomial, Nat.choose]
  | succ n ih =>
      have hsecond :=
        fibonacci_recurrence_polynomial_coefficients.2.1 (n + 1)
      rw [show n + 1 + 5 = (n + 4) + 2 by omega,
        fibonacciRecurrencePolynomial, coeff_add, coeff_X_mul]
      rw [ih, hsecond]
      have hchoose :
          (Nat.choose (n + 1 + 2) 2 : ℤ) =
            (n + 2 : ℤ) + (Nat.choose (n + 2) 2 : ℤ) := by
        rw [show n + 1 + 2 = (n + 2) + 1 by omega,
          Nat.choose_succ_succ]
        simp
      rw [hchoose]
      omega

#print axioms fibonacci_recurrence_polynomial_third_coefficient

end D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient
