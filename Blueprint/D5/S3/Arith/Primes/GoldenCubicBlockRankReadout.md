# Rank readouts for all cubic Lucas lags

## Abstract

Exact valuations of native cubic Lucas lags at every ordinary prime.

**Theorem 1.1 (Rank hit, entry depth, and the index quotient).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.valuation_eq_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.valuation_eq_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an odd prime, a positive Fibonacci index has depth zero unless its original entry rank divides the index. If it divides, the depth equals the entry depth plus the depth of the index divided by the rank.

**Theorem 1.2 (Exact native block lag depth without a witness hypothesis).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_lag`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct levels, the lag depth is the sum of the two Fibonacci rank readouts at the sum and difference indices, with an extra one at five. This holds also for primes which never divide any Lucas block.

**Theorem 1.3 (Exact residue collision at every odd-prime precision).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two readings coincide modulo the given prime power exactly when its exponent fits within their computed joint rank depth.

**Theorem 1.4 (All ordinary primes, including the first dyadic step).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_all_prime_lag`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_all_prime_lag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd-prime readouts combine with the dyadic clock to classify every prime. At two, the level-zero block and every later block differ already modulo two, and two positive levels obey the exact dyadic lag law.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_all_prime_lag`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_collision`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.cubic_block_odd_prime_rank_lag`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockRankReadout.valuation_eq_readout`
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeStepLift](FibonacciPrimeStepLift.md)
- Dependency: [D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation](FibonacciPrimeToIndexValuation.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct](GoldenCubicBlockFibonacciLagProduct.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicDyadicClock](GoldenCubicDyadicClock.md)
