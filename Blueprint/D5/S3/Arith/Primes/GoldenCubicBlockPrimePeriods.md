# Golden Cubic Block Prime Periods

## Abstract

Prime factors of the two golden cubic blocks have exact Fibonacci matrix periods.

**Theorem 1.1 (The Lucas block).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_b_prime_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_b_prime_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j at least one, every prime factor p of L_(3^j)^2 + 3 has Fibonacci matrix period exactly 2 times 3^(j+1). The Lucas value at 3^(j+1) vanishes modulo p. The quadratic trace and norm identity then makes the golden generator return at twice that index; its first Fibonacci zero rules out an earlier return.

**Theorem 1.2 (The Fibonacci block).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_c_prime_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_c_prime_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j at least one, every prime factor p of L_(3^j)^2 + 1 has Fibonacci matrix period exactly 4 times 3^(j+1). At the first Fibonacci zero, the golden generator squares to minus one by Cassini's identity. The block is odd, so minus one is not one modulo p; its residual order is four.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_b_prime_period`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_c_prime_period`
- Dependency: [D5/S3/Arith/GoldenFibonacciModulusPeriod](../GoldenFibonacciModulusPeriod.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockRanks](GoldenCubicBlockRanks.md)
