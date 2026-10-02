# Nonsquares in Higher Odd Prime-Power Layers

## Abstract

All higher odd prime-power Fibonacci quotients are positive nonsquares beyond an explicit prime threshold.

**Theorem 1.1 (An analytic obstruction for recurrence polynomials and Fibonacci quotients).**

Lean statement: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r at least 119, the recurrence polynomial U_(2r+1) takes a nonsquare value at every integer x greater than two satisfying x^2 - 4 > 128 times 6^r. Pairing its complex roots yields factors X^2 + lambda_i with 0 at most lambda_i less than four. Reversing and contracting the recurrence polynomial produces an integral polynomial whose linear coefficient is odd. The half-binomial expansion then has odd dyadic coefficient numerators; its analytic square-root branch obeys a Cauchy coefficient bound. The dyadic analytic integer obstruction excludes an integer square root. For every odd n at least 2r+1, the Fibonacci quotient F_((2r+1)n)/F_n is positive and nonsquare. In particular, for every prime q at least 239 and every k at least one, F_(q^(k+1))/F_(q^k) is positive and nonsquare.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare`
- Dependency: [D5/S3/Arith/Primes/DyadicSeriesIntegerObstruction](DyadicSeriesIntegerObstruction.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddBridge](FibonacciRecurrencePolynomialOddBridge.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciRecurrencePolynomialRoots](FibonacciRecurrencePolynomialRoots.md)
- Dependency: [D5/S3/Arith/Primes/GoldenLucasNonsquareThreshold](GoldenLucasNonsquareThreshold.md)
