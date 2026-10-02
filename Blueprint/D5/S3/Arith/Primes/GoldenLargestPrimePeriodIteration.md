# Largest-prime period iteration

## Abstract

The largest prime above five loses exactly its original Fibonacci depth at each period iteration.

**Theorem 1.1 (Exact depth loss for every positive modulus).**

Lean statement: `D5/S3/Arith/Primes/GoldenLargestPrimePeriodIteration.golden_largest_prime_period_iteration`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenLargestPrimePeriodIteration.golden_largest_prime_period_iteration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be positive and let P greater than five be its largest prime divisor. Write a for the P-adic valuation of m and h_P for the P-adic valuation of the Fibonacci number at the first positive index divisible by P. For every n at least zero, the P-adic valuation of the n-th iterate of the Fibonacci matrix period is a minus n times h_P, truncated at zero. The prime P divides that iterate exactly when n is less than the ceiling of a divided by h_P. Thus P first disappears at that ceiling and never returns. Every positive fixed point of the period function has no prime divisor greater than five. If the periods of m and m squared agree, then h_P is at least twice a. The theorem does not classify the remaining fixed points or bound the total time until an iterate becomes fixed.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenLargestPrimePeriodIteration.golden_largest_prime_period_iteration`
- Dependency: [D5/S3/Arith/GoldenFibonacciModulusPeriod](../GoldenFibonacciModulusPeriod.md)
- Dependency: [D5/S3/Arith/GoldenPrimePowerOrder](../GoldenPrimePowerOrder.md)
- Dependency: [D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod](GoldenPrimePowerMatrixPeriod.md)
