# Mixed Prime History Counts

## Abstract

Mixed Prime History Counts.

**Theorem 1.1 (Reachability and finite fibres).**

Lean statement: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.reachable_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.reachable_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting at one, each letter adds or multiplies by its labelled prime. Every positive integer is reached by at least one finite word. Every step strictly increases the state, bounding both word length and prime labels at a fixed endpoint, so only finitely many such words exist.

**Theorem 1.2 (Counting by the last letter).**

Lean statement: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.history_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.history_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an endpoint n at least two, each history has a unique last letter. An additive prime q is smaller than n and leaves a predecessor ending at n minus q. A multiplicative prime q divides n and leaves a predecessor ending at n divided by q. Summing these finite predecessor counts gives the total. The two typed letters remain distinct even when their numerical actions agree.

**Theorem 1.3 (Counting histories of a fixed length).**

Lean statement: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.length_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.length_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive length k and endpoint n at least two, deleting the last letter leaves length k minus one. The same additive and multiplicative predecessor partition therefore gives the recurrence for histories of exactly length k. The empty word starts and ends at one and provides the length zero convention.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.history_recurrence`
- Truth anchor: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.length_recurrence`
- Truth anchor: `D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.reachable_finite`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../../ObserverMemory/Prediction/ControlledBehaviorUniversality.md)
