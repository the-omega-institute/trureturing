# Fibonacci Recurrence Polynomial Coefficients

## Abstract

The first two nonzero coefficient layers of the Fibonacci recurrence polynomial.

**Theorem 1.1 (Near-leading coefficients).**

Lean statement: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define U_0=0 and U_1=1, with U_(m+2)=X U_(m+1)+U_m. For every m at least one, U_m has degree m-1 and leading coefficient one. For every m at least three, the coefficient at X^(m-3) equals m-2. Thus at each odd index q=2r+1 with r at least one, this coefficient is the odd number q-2.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients`
