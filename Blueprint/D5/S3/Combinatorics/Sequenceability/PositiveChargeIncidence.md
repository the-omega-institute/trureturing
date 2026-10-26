# Original incidence and positive component charge

## Abstract

Original incidence and positive component charge

**Theorem 1.1 (Quotient labels detect the original integer Boolean rows).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.quotient_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.quotient_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary original coordinate type X and integer submodule M, quotientLabel M x is the class of the original unit vector at x. A finite sum of these labels vanishes exactly when the coefficient-one indicator row of its original support belongs to M. No saturation or scaled relation is substituted.

**Theorem 1.2 (Every Complete row is a disjoint coefficient-one sum).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.complete_disjoint_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.complete_disjoint_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing disjoint minimal-zero decomposition to the quotient labels. Every Complete support A is the union of an independent subfamily Q of the full original minimalFamily, and row A equals the sum of row S over S in Q. This adapter uses the existing recursive supplier and supplies the negative-selector argument and the original avoiding-word consumers.

**Theorem 1.3 (The actual ordinary charge gcd forces original positive geometry).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.original_positive_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.original_positive_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume q belongs to Omega, at least two original minimal rows contain q, every other original coordinate belongs to at most two minimal rows, and ordinaryChargeGCD equals the number of q-terminals. Then a connected ungrounded bipartite RawBlock has exactly the full terminal family on its left. Either a right row meets every terminal, or an actual Geometry, nonuniversal right row, distinct terminal endpoints and an injective endpoint rank are constructed.

The charge bound and integer gcd select the component. Its original q equation forces potential injectivity, and disjoint Boolean decomposition excludes negative selectors. Delete and pair test potentials identify the full terminal side and force common-neighbour coverage. ComponentSides identifies this incidence inventory with the actual ordinary-component inventory. The right_port, left_ne_right, no_q_right and no_same_left lemmas expose the exact port suppliers and side separation consumed by the subsequent universal-word construction.

All statements retain the PositiveChargeGeometry declaration namespace. PositiveChargeGeometry consumes this incidence API for exterior colouring, the universal frame and the full positive-charge target. The original coefficient-one H ledger follows from integer span induction. These are symbolic incidence results; no zero-charge, full Good or adaptive merge conclusion is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.complete_disjoint_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.original_positive_geometry`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence.quotient_zero_iff`
- Dependency: [D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering](DisjointMinimalZeroOrdering.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PositiveChargePorts](PositiveChargePorts.md)
