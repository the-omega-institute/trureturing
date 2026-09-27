# Golden Cubic Block Ranks

## Abstract

Prime factors of the two Lucas cubic blocks have exact first-zero ranks and original depths.

**Theorem 1.1 (The Fibonacci block).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_c_prime_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_c_prime_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j at least one, put x = L_(3^j) and C = x^2 + 1. Every prime p dividing C first divides a Fibonacci number at index 3^(j+1), and its valuation in C equals its valuation at that first Fibonacci zero. The identity F_(3^(j+1)) = F_(3^j) C supplies the zero; the Lucas discriminant excludes an earlier zero at 3^j.

**Theorem 1.2 (The Lucas block).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_b_prime_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_b_prime_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j at least one, put x = L_(3^j) and B = x^2 + 3. Every prime p dividing B first divides a Fibonacci number at index 2 times 3^(j+1). Five is a quadratic residue modulo p, and the valuation of p in B is its original Fibonacci entry valuation. The Lucas discriminant excludes earlier zeros; F_(2r) = F_r L_r at r = 3^(j+1) identifies the valuation.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_b_prime_rank`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_c_prime_rank`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
