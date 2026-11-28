# The profinite cubic Lucas clock

## Abstract

The native cubic Lucas trajectory realizes every compatible absolute-time clock.

**Definition 1.1 (All compatible eventual states).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.nativeClock`

*Formalization.* `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.nativeClock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact native periods are cofinal among all positive time moduli. The resulting clock labels the entire eventual inverse-limit family.

**Theorem 1.2 (The cubic update advances time by one).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.nativeClock_next`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.nativeClock_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Addition by one agrees at every observation modulus with the original cubic polynomial.

**Theorem 1.3 (Finite blocks are not eventual clock points).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.finite_block_not_eventual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.finite_block_not_eventual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each finite block has a three-adic observation separating it from every compatible eventual family.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.finite_block_not_eventual`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.nativeClock`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicProfiniteClock.nativeClock_next`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicClockCofinality](GoldenCubicClockCofinality.md)
- Dependency: [D5/S3/Arith/Primes/ProfiniteObservationClock](ProfiniteObservationClock.md)
