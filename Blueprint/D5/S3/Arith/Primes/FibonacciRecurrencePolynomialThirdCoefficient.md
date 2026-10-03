# Fibonacci Recurrence Polynomial Third Coefficient

## Abstract

The third near-leading coefficient of the Fibonacci recurrence polynomial.

**Theorem 1.1 (Third near-leading coefficient).**

Lean statement: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the recurrence U_0=0, U_1=1, and U_(m+2)=X U_(m+1)+U_m, the coefficient of X^n in U_(n+5) is the binomial coefficient choose(n+2,2). Equivalently, for m at least five this is the third near-leading coefficient at degree m-5, equal to (m-3)(m-4)/2.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient`
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients](FibonacciRecurrencePolynomialCoefficients.md)
