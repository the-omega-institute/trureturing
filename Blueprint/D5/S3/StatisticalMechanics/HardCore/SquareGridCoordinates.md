# SquareGridCoordinates

## Abstract

Exact correspondence between grid geometry and actual independent-set messages.

**Definition 1.1 (The actual infinite square grid).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.squareGrid`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.squareGrid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four nearest-neighbor edges are defined on the previously owned integer-pair coordinate carrier.

**Definition 1.2 (Center an arbitrary root).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shiftTo`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shiftTo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit inverse adds the root coordinates back.

**Definition 1.3 (The actual recenter map is bijective).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenterEquiv`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenterEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map is the existing OrderedGridMemory.recenter. The inverse undoes the translation and quarter-turn.

**Theorem 1.4 (Translations preserve and reflect adjacency).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shift_adj_iff`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shift_adj_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This checks the actual coordinate formulas rather than assuming a graph automorphism.

**Theorem 1.5 (Recentered edges are exactly grid edges).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_adj_iff`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_adj_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All three maps preserve and reflect the nearest-neighbor relation.

**Theorem 1.6 (The selected neighbor becomes the origin).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_direction`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This fixes the marked vertex in the transported child ratio.

**Definition 1.7 (Actual grid partition sums).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridPartition`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is an abbreviation for the existing independent-configuration sum at constant activity.

**Definition 1.8 (Actual marked ratios over a field).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridVacancy`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridVacancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Numerator and denominator are actual grid partitions. Division is total as a field operation; legitimate recursive cancellation requires separately proved nonzero denominators.

**Theorem 1.9 (Exact partition invariance).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.partition_recenter`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.partition_recenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general configuration-bijection theorem is applied to the actual grid map. The conclusion holds in every commutative semiring.

**Theorem 1.10 (Exact marked-ratio invariance).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_recenter`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_recenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both numerator and denominator transport. Equality at zero denominators is an equality of total field expressions, not a claim of analytic regularity.

**Theorem 1.11 (Every marked root can be centered).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_shift`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem concerns constant activities. General inhomogeneous weights are covered only by the explicit pullback in PartitionRelabeling.

**Theorem 1.12 (The old root is removed before every child).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.before_child_subset_erase`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.before_child_subset_erase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prescribed deletion always includes the current origin.

**Theorem 1.13 (Every child is strictly smaller).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.advance_card_lt`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.advance_card_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Image cardinality and actual root deletion give the well-founded measure needed for the subsequent nonvanishing induction.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.advance_card_lt`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.before_child_subset_erase`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridPartition`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridVacancy`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.partition_recenter`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenterEquiv`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_adj_iff`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_direction`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shiftTo`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shift_adj_iff`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.squareGrid`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_recenter`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_shift`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory](OrderedGridMemory.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling](PartitionRelabeling.md)
