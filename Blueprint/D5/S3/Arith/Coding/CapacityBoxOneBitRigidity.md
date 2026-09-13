# Capacity Box One-Bit Rigidity

## Abstract

Capacity-box unit-edge colours depend only on the axis and layer, and different axes use disjoint sets of bits.

**Definition 1.1 (Colour of a unit Boolean edge).**

Lean statement: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour`

*Formalization.* `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The colour of a unit edge is the unique coordinate at which its two Boolean words differ.

**Definition 1.2 (Directed capacity edge).**

Lean statement: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge`

*Formalization.* `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A unit edge increases one capacity coordinate by one while fixing every other coordinate.

**Definition 1.3 (One-bit capacity code).**

Lean statement: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding`

*Formalization.* `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A one-bit capacity code is injective and maps every unit edge to two Boolean words at Hamming distance one.

**Definition 1.4 (Increase one coordinate).**

Lean statement: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise`

*Formalization.* `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indicated coordinate is increased by one when its value is below capacity.

**Definition 1.5 (Colour of a capacity edge).**

Lean statement: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour`

*Formalization.* `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The colour of a capacity edge is the unique bit changed by its image.

**Theorem 1.6 (Colours are constant across a layer).**

Lean statement: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.colour_depends_only_on_layer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.colour_depends_only_on_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two edges increasing the same axis from the same starting value have the same colour, regardless of their other coordinates. Lowering those coordinates one at a time connects each edge to the same axis fibre.

**Theorem 1.7 (Different axes use different colours).**

Lean statement: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.different_axes_distinct_colours`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.different_axes_distinct_colours` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two layer edges on distinct axes can be transported to edges with a common starting state. If they changed the same bit, their other endpoints would have equal codes, contradicting injectivity.

## References

- Truth anchor: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding`
- Truth anchor: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge`
- Truth anchor: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.colour_depends_only_on_layer`
- Truth anchor: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.different_axes_distinct_colours`
- Truth anchor: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour`
- Truth anchor: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise`
- Truth anchor: `D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour`
- Dependency: [D5/S1/Ledger/BoundedTimeSlice](../../../S1/Ledger/BoundedTimeSlice.md)
