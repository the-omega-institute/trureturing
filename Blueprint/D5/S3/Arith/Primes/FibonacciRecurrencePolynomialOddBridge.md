# Odd-Index Fibonacci Recurrence Bridge

## Abstract

The odd-index Fibonacci quotient bridge for the recurrence polynomial.

**Theorem 1.1 (Odd-index recurrence bridge).**

Lean statement: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddBridge.odd_fibonacci_recurrence_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddBridge.odd_fibonacci_recurrence_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd positive index n and every natural m, the Fibonacci recurrence polynomial U_m evaluated at the Lucas number L_n satisfies F_n U_m(L_n) = F_(mn), and the rational quotient F_(mn)/F_n equals the same polynomial value. The identity follows from the quadratic relation for the nth power of the golden generator and its Fibonacci coordinate recurrence.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddBridge.odd_fibonacci_recurrence_bridge`
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients](FibonacciRecurrencePolynomialCoefficients.md)
