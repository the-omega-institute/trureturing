# Primitive ternary primes for the Lucas residue clock

## Abstract

Prime divisors of a third cyclotomic factor supply exact ternary orders for the Lucas residue clock.

**Theorem 1.1 (Every positive power of three is the exact order of nine at some prime).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicPrimitiveTernaryPrime.exists_prime_orderOf_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicPrimitiveTernaryPrime.exists_prime_orderOf_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a prime factor of the third cyclotomic polynomial evaluated at the preceding ternary power of nine. The geometric-sum identity bounds the order; collapsing to the preceding power would force the prime to divide three. The witness prime is outside two, three, and five.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicPrimitiveTernaryPrime.exists_prime_orderOf_nine`
