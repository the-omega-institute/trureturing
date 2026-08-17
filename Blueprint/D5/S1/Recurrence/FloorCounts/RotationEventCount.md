# Rotation Event Count

## Abstract

Floor-difference rotation events telescope and have discrepancy strictly below one.

**Theorem 1.1 (Bounded rotation event count).**

$$bounded event count$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FloorCounts/RotationEventCount.bounded_event_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event weight is the difference of consecutive floor samples along a real rotation. Summing over a finite window telescopes to the endpoint floor difference, and the resulting count differs from the real displacement by strictly less than one.

Pinned Mathlib was searched before proving. The proof uses the existing Int.floor_add_fract, Int.fract_nonneg, and Int.fract_lt_one lemmas, together with ring and linear arithmetic; no floor or equidistribution theorem is reproved. The formal scope is the finite event-count identity and its unit discrepancy bound.

## References

- Truth anchor: `D5/S1/Recurrence/FloorCounts/RotationEventCount.bounded_event_count`
