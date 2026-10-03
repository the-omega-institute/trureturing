# Golden Cubic Block Period Iteration

## Abstract

Selected golden cubic blocks have an exact joint matrix period and a determined period trajectory.

**Theorem 1.1 (Period of a selected block product).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockPeriodIteration.cubic_block_product_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockPeriodIteration.cubic_block_product_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite sets I and J of positive indices with nonempty union, multiply the distinct C blocks selected by I and the distinct B blocks selected by J. Its Fibonacci matrix period is 4 times 3^(K+1) when I is nonempty and 2 times 3^(K+1) otherwise, where K is the largest selected index. The selected C product divides F_(3^(K+1)); the selected B product divides L_(3^(K+1)). These whole-product returns give upper bounds, while a prime factor of a block at the largest index gives the matching lower bound. Coprimality of the two families combines the periods by CRT.

**Theorem 1.2 (Complete iteration and first arrival).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockPeriodIteration.cubic_block_product_first_arrival`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockPeriodIteration.cubic_block_product_first_arrival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same selected block product M and largest index K, the first period iterate is the block-product period above. At iteration 2+t the value is 8 times 3^max(1,K-t), for every t at least zero. The trajectory first reaches 24 at iteration K+1, and 24 is a fixed point of the period map. The proof computes the exact order modulo powers of three and the small moduli 2, 4, and 8, then uses CRT and induction. The conclusion concerns the selected integer blocks, not arbitrary moduli or WSS prime depths.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockPeriodIteration.cubic_block_product_first_arrival`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockPeriodIteration.cubic_block_product_period`
- Dependency: [D5/S3/Arith/GoldenFibonacciModulusPeriod](../GoldenFibonacciModulusPeriod.md)
- Dependency: [D5/S3/Arith/GoldenPrimePowerOrder](../GoldenPrimePowerOrder.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods](GoldenCubicBlockPrimePeriods.md)
