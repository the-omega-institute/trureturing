# Synchronous prime clocks in one Lucas tail

## Abstract

Two primes observing the same Lucas tail have a precise shared-time constraint.

**Theorem 1.1 (Exact compatibility of two prime clocks).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two separately observed residues occur together at a single later block exactly when their time labels agree modulo the gcd of the individual periods.

**Theorem 1.2 (The joint clock has the lcm kernel).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two block indices give the same pair of residues precisely when their difference is a multiple of the lcm of the periods. The initial offset may be chosen after both prime witnesses.

**Definition 1.3 (Enumerating the compatible residue pairs).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.compatibleResiduePairs`

*Formalization.* `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.compatibleResiduePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Time labels below the lcm biject with precisely the compatible pair labels, including when the periods are not coprime.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.compatibleResiduePairs`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_collision`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockJointClock.synchronous_pair_exists`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage](GoldenCubicBlockTailOrbitImage.md)
