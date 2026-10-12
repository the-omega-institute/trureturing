# Marked-edge bad events

## Abstract

The fixed-label sample space and collision events at marked edges.

**Definition 1.1 (Labelings with two fixed edge labels).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.MarkedLabeling`

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.MarkedLabeling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sample space consists of equivalences from the edge type to Fin m whose values on the two marked edges are zero and one.

**Definition 1.2 (Positive labels).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.markLabel`

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.markLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label of an edge is one plus its zero-based finite value.

**Definition 1.3 (An additive collision).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.AdditiveTriple`

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.AdditiveTriple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An additive collision means that one of three edge labels is the sum of the other two.

**Theorem 1.4 (Size of the marked sample space).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_markedLabeling`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_markedLabeling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m edges and two distinct marked edges, the sample space has (m-2)! elements.

**Theorem 1.5 (The event containing both marked edges).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_bad_both_marked`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_bad_both_marked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triple with marked labels one and two is bad exactly when the third label is three. There are (m-3)! such labelings.

**Theorem 1.6 (The event containing one marked edge).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_bad_single_marked_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_bad_single_marked_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed incident label delta equal to one or two, a bad triple's two free labels differ by delta. Their smaller value has m-2-delta choices and they have two edge orders. Each assignment leaves (m-4)! extensions, giving an upper bound of 2*(m-2-delta)*(m-4)!.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.AdditiveTriple`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.MarkedLabeling`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_bad_both_marked`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_bad_single_marked_le`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.card_markedLabeling`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.markLabel`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphCounting](CubicARGraphCounting.md)
