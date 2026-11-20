# Fibonacci valuation at an odd-prime index step

## Abstract

An odd prime divisor of a Fibonacci value gains exactly one valuation digit when it multiplies the positive index.

**Theorem 1.1 (Binomial expansion with a divisible quadratic remainder).**

Lean statement: `D5/S3/Arith/Primes/FibonacciPrimeStepLift.prime_first_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciPrimeStepLift.prime_first_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any commutative ring, expand the p-th power of a plus b times z, where p is an odd prime and its image divides b. After removing the constant and linear terms, the remainder is divisible by p times b squared. The intermediate binomial coefficients provide the prime factor; in the last term, the factor comes from b.

**Theorem 1.2 (One additional digit in the native Fibonacci valuation).**

Lean statement: `D5/S3/Arith/Primes/FibonacciPrimeStepLift.fibonacci_valuation_prime_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FibonacciPrimeStepLift.fibonacci_valuation_prime_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an odd prime p divides the Fibonacci value at positive index r, then its valuation at index p times r is exactly one more. In the golden integer ring, the quotient of the new Fibonacci coordinate by p times the old coordinate reduces to a nonzero power of the preceding Fibonacci value modulo p. This uses no split-prime hypothesis and does not determine the valuation at the first zero index.

## References

- Truth anchor: `D5/S3/Arith/Primes/FibonacciPrimeStepLift.fibonacci_valuation_prime_step`
- Truth anchor: `D5/S3/Arith/Primes/FibonacciPrimeStepLift.prime_first_order`
- Dependency: [D5/S0/Carrier/Ring](../../../S0/Carrier/Ring.md)
