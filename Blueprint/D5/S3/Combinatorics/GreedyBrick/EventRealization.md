# Events Realized by Rest Histories

## Abstract

A genuine first-zero rest trace realizes exact-reset event laws and total same-bin successors.

A rest history supplies actual RestState values and a RestEventStep at every transition. A rest trace additionally starts at endpoint one with capacity list [1] and initial label one, and has unbounded capacity-list length. These are intermediate source premises; this result does not construct the literal brick trajectory or prove the original OEIS identity.

**Theorem 1.1 (Finite capacity budget).**

Lean statement: `D5/S3/Combinatorics/GreedyBrick/EventRealization.no_reset_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GreedyBrick/EventRealization.no_reset_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive bin present at endpoint e with capacity c, suppose its label does not occur in the next d transitions. There is an actual final capacity r, with r plus the number of higher events equal to c. Final height is at most initial height plus that same higher-event count. No initialization or unbounded-height premise is needed. Absent coordinates receive no default value.

**Theorem 1.2 (Every label returns).**

Lean statement: `D5/S3/Combinatorics/GreedyBrick/EventRealization.future_same_bin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GreedyBrick/EventRealization.future_same_bin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every event e of a rest trace, some event f strictly after e has the same bin. If no such reset existed, unbounded higher births would exceed the finite capacity budget of that bin. Chronological EventLaws alone are insufficient for this existence statement.

**Theorem 1.3 (Exact event-law realization).**

Lean statement: `D5/S3/Combinatorics/GreedyBrick/EventRealization.event_laws_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GreedyBrick/EventRealization.event_laws_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The EventSequence with the trace's endpoints, labels and heights, least indices attaining each positive height, and greatest earlier same-bin indices satisfies every EventLaws field. Reset balance follows by telescoping the real capacity from its prior endpoint reset to zero before the next reset, then splitting higher events into births and renewals. Birth at height zero is unused; positive births exist by unbounded height. Predecessors are used only at renewals.

**Theorem 1.4 (Total immediate successors and inverse laws).**

Lean statement: `D5/S3/Combinatorics/GreedyBrick/EventRealization.successor_inverse_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GreedyBrick/EventRealization.successor_inverse_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The least future same-bin index exists for every event, is a renewal, has that event as its immediate predecessor, and contains no intervening same-bin event. Conversely every renewal is the successor of its predecessor. This includes event zero and all positive-height births.

## References

- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/EventRealization.event_laws_realization`
- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/EventRealization.future_same_bin`
- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/EventRealization.no_reset_budget`
- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/EventRealization.successor_inverse_laws`
- Dependency: [D5/S3/Combinatorics/GreedyBrick/SuccessorBand](SuccessorBand.md)
