# Chebyshev Representation of the Recurrence Polynomial

## Abstract

The plus-recurrence polynomial is represented by a complex-scaled Chebyshev polynomial of the second kind.

**Theorem 1.1 (Complex Chebyshev bridge).**

Lean statement: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialChebyshev.fibonacci_recurrence_polynomial_chebyshev`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialChebyshev.fibonacci_recurrence_polynomial_chebyshev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, mapping the integer recurrence polynomial at index k+1 into the complex polynomial ring gives (-i)^k times the Chebyshev U polynomial at index k, composed with the variable iX/2.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialChebyshev.fibonacci_recurrence_polynomial_chebyshev`
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients](FibonacciRecurrencePolynomialCoefficients.md)
