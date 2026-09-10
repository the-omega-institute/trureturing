# SquareGridRootMessages

## Abstract

Exact correspondence between grid geometry and actual independent-set messages.

**Definition 1.1 (The exact existing root frame).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootFrame`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This equivalence realizes the coordinate map already inside rootDomain. Its agreement with the original domain is proved, without accessing private names.

**Theorem 1.2 (All four frames preserve grid edges).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_frame_adj_iff`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_frame_adj_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjacency is preserved and reflected by every root coordinate map.

**Definition 1.3 (The ordered root prefix).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootEarlier`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootEarlier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This lists exactly those neighbors that precede the selected first child.

**Theorem 1.4 (The actual first-child factor).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The marked vacancy on the original rootDomain equals its successive unrotated neighbor ratio.

**Theorem 1.5 (The genuine four-child root formula).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_partition_recursion`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_partition_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This uses proper-domain nonvanishing, without assuming the root partition is nonzero or applying a three-child contraction bound to the root.

**Theorem 1.6 (Initialize the certified geometric type).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_context`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_context` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every present first child contains its new root, is compatible with the existing type-zero mask, and has fewer vertices than the original graph domain.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootEarlier`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootFrame`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_context`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_vacancy`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_frame_adj_iff`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_partition_recursion`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/SquareGridMessages](SquareGridMessages.md)
