# Cofinal native Lucas clocks

## Abstract

The eventual native Lucas clocks observe every positive time modulus.

**Theorem 1.1 (Divisibility of observation moduli implies divisibility of periods).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_dvd_of_modulus_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_dvd_of_modulus_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A late return at the finer observation modulus gives a late return at the coarser modulus, so its least positive period is a multiple.

**Theorem 1.2 (Every ternary time digit can be observed at a prime other than three).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.ternary_time_observed_at_other_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicClockCofinality.ternary_time_observed_at_other_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a cyclotomic prime where the order of nine is the requested power of three. A sufficiently fine signed Lucas clock at that same prime retains the entire ternary time digit window.

**Theorem 1.3 (Every time modulus divides a native observation period).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_cofinal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Own-prime growth and cross-prime ternary growth supply every prime power, and a common multiple of the observation moduli combines these time requirements into one finite clock.

**Theorem 1.4 (Three separates every actual reading yet loses time in the limit).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_block_isolated_at_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_block_isolated_at_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three-adic precision indexed by one actual level separates that level from all the other actual levels. Conversely, each fixed precision eventually reads one.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_block_isolated_at_three`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_cofinal`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.native_period_dvd_of_modulus_dvd`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicClockCofinality.ternary_time_observed_at_other_prime`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock](GoldenCubicBlockSignedRankClock.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed](GoldenCubicBlockTailPeriodClosed.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicPrimitiveTernaryPrime](GoldenCubicPrimitiveTernaryPrime.md)
