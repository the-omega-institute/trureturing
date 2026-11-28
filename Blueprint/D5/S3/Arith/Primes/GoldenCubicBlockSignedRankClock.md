# Exact native cubic Lucas orbits modulo every integer

## Abstract

The native cubic Lucas orbit has a sharp transient and period at every positive modulus.

**Theorem 1.1 (Fibonacci rank yields the exact signed period).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.canonical_prime_power_period`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.canonical_prime_power_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Away from two, three, and five the three-primary part of the Fibonacci rank sets the exact transient length. A single global sign modulo the rank core times a power of the prime gives the period.

**Theorem 1.2 (All collisions at every positive integer modulus).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transient is the maximum of the prime-power transients. The period is the least common multiple of the prime-power periods. Distinct indices coincide if and only if the earlier index is past the transient and the period divides the lag.

**Theorem 1.3 (Exactly the transient plus one cycle).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_residue_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_residue_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact number of attained residues is the transient length plus one period, including modulus one. The entire initial transient and first cycle are representatives with no repetition.

**Theorem 1.4 (The period doubles at thirteen).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_thirteen_periods`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_thirteen_periods` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native period is three modulo thirteen and six modulo one hundred sixty-nine. Squaring the sign test modulo the composite rank modulus would incorrectly keep period three.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.canonical_prime_power_period`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_collision`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_residue_count`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_thirteen_periods`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockRankReadout](GoldenCubicBlockRankReadout.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic](GoldenCubicBlockThreeAdic.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicFiveClock](GoldenCubicFiveClock.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicSignedOrder](GoldenCubicSignedOrder.md)
- Dependency: [D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization](ModularOrbitPrimePowerFactorization.md)
