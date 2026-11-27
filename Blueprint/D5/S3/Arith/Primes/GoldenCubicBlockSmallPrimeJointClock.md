# Synchronizing the small-prime Lucas readouts

## Abstract

The two small-prime readouts of one Lucas block compose differently with odd witness clocks.

**Theorem 1.1 (Exact compatibility of dyadic and odd witness readings).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.dyadic_witness_pair_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.dyadic_witness_pair_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The time labels have to agree modulo the greatest common divisor of their periods. For witnesses congruent to three modulo four, the odd witness period is odd and no constraint remains.

**Theorem 1.2 (A witnessed failure of dyadic independence).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.native_dyadic_parity_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.native_dyadic_parity_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime 1277209 occurs at level six to depth one and has an even base-nine clock. At precision 256 and 1277209 cubed, opposite time parities give two separately attainable but incompatible readings.

**Theorem 1.3 (A transient at three fixes the time, but the fixed residue does not).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.three_witness_pair_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.three_witness_pair_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuinely transient reading modulo a power of three can occur at only one time. Once its fixed residue is reached, every available periodic witness phase can be represented at a sufficiently late index.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.dyadic_witness_pair_exists`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.native_dyadic_parity_obstruction`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockSmallPrimeJointClock.three_witness_pair_exists`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockJointClock](GoldenCubicBlockJointClock.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic](GoldenCubicBlockThreeAdic.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicDyadicClock](GoldenCubicDyadicClock.md)
