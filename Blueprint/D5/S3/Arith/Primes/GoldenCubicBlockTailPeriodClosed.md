# Closed least periods of cubic Lucas block tails

## Abstract

The least congruence period of a later Lucas-block stream separates its Lucas depth from the base-three Fermat depth.

**Theorem 1.1 (The base-three threshold for lifting the order of nine).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.orderOf_nine_prime_power`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.orderOf_nine_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd prime other than three, let t be the order of nine modulo p and e the valuation of three to the power p minus one, minus one. At positive precision r the order is t times p to the power max(0,r-e).

**Theorem 1.2 (Least positive period at every precision).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_least`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime divisor of an earlier Lucas block, let h be its valuation in that block. Later blocks are constant modulo p^a through a=2h. Above that precision the least period is t times p to the power max(0,a-2h-e), and all return periods are multiples of it. This does not determine which blocks have an exponent-one factor.

**Theorem 1.3 (Recover both depths from the period profile).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.cubicTailPeriod_profile_cutoffs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.cubicTailPeriod_profile_cutoffs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The period one plateau ends exactly at 2h and the first nontrivial period plateau ends at 2h+e. The separation of the two depths can therefore be read back from the stream itself.

**Theorem 1.4 (All precisions for the first block prime 19).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_nineteen`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_nineteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p=19 and the first block, the computed period is one through precision two and 9 times 19 to the power a-3 thereafter.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.cubicTailPeriod_profile_cutoffs`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_least`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.golden_cubic_tail_period_nineteen`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed.orderOf_nine_prime_power`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockLagValuation](GoldenCubicBlockLagValuation.md)
