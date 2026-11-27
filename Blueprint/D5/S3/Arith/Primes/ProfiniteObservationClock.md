# Profinite clocks from eventual observations

## Abstract

Exact eventual collisions and period cofinality recover every absolute time label.

**Definition 1.1 (Exact finite absolute labels).**

Lean statement: `D5/S3/Arith/Primes/ProfiniteObservationClock.finiteClock`

*Formalization.* `D5/S3/Arith/Primes/ProfiniteObservationClock.finiteClock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equality at sufficiently late observations is exactly congruence modulo the period. Labeling an eventual state by the original observation index gives a bijection with the finite clock.

**Definition 1.2 (Cofinal periods recover the full clock).**

Lean statement: `D5/S3/Arith/Primes/ProfiniteObservationClock.cofinalClock`

*Formalization.* `D5/S3/Arith/Primes/ProfiniteObservationClock.cofinalClock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A common refinement makes reduction from any sufficiently divisible observation period independent of choice. This reconstructs all compatible time labels, not only those from natural indices.

**Theorem 1.3 (Advancement is addition by one).**

Lean statement: `D5/S3/Arith/Primes/ProfiniteObservationClock.cofinalClock_next`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ProfiniteObservationClock.cofinalClock_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence carries translation by one to the inverse-limit shift. The generic shift is invertible and agrees with a native recurrence on each observed coordinate.

## References

- Truth anchor: `D5/S3/Arith/Primes/ProfiniteObservationClock.cofinalClock`
- Truth anchor: `D5/S3/Arith/Primes/ProfiniteObservationClock.cofinalClock_next`
- Truth anchor: `D5/S3/Arith/Primes/ProfiniteObservationClock.finiteClock`
