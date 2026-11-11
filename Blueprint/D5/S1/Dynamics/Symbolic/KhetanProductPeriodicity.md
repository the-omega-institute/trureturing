# Product exact-cover bridge at the six-cell boundary

## Abstract

Exact-cover product fibres feed the six-cell residue dichotomy.

This module isolates the two-dimensional bridge for a product tile {0,1} × {0,b,c}. The one-dimensional theorem three_point_tiling_residue is an explicit hypothesis of the bridge: it is the unresolved Newman/Fourier input and is not proved or hidden here. Given that input, the exact-cover window forces adjacent columns to be disjoint and to form a residue-labelled XOR partition, after which the existing three_residue_column_dichotomy supplies the horizontal/vertical period alternative.

**Definition 1.1 (Indicator of a column anchor).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.anchorBit`

*Formalization.* `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.anchorBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

anchorBit(T,x,y) is the natural-number indicator of membership of (x,y) in the anchor set T. It is used to express exact coverage as a sum of zero-one contributions.

**Definition 1.2 (One-dimensional three-point window count).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.oneDWindowCount`

*Formalization.* `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.oneDWindowCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

oneDWindowCount(S,b,c,y) sums the indicators of S at the three translated sites y, y-b, and y-c. The separate three_point_tiling_residue input consumes the assertion that this count is exactly one at every y.

**Definition 1.3 (Two-column product window count).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.productWindowCount`

*Formalization.* `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.productWindowCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

productWindowCount(T,b,c,x,y) sums the six possible anchors from columns x-1 and x at the three vertical offsets 0, b, and c. The hypothesis productWindowCount = 1 is the exact unique-cover condition for the product tile.

**Theorem 1.4 (Exact-cover product fibres force a period).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.product_three_exact_cover_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.product_three_exact_cover_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume b and c are nonzero, distinct, and coprime. Supply explicitly the one-dimensional theorem three_point_tiling_residue for every predicate S satisfying the three-point window count. If every two-column product window has count one, the theorem derives disjoint adjacent columns and a residue/XOR partition.

The conclusion is exactly the existing residue dichotomy: either T(x+2,y) ↔ T(x,y) for all x,y, or T(x,y+3) ↔ T(x,y) for all x,y. This is a conditional product branch, not a resolution of the full six-cell orbit-closure problem; the one-dimensional rigidity and orbit-closure extraction remain separate obligations.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.anchorBit`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.oneDWindowCount`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.productWindowCount`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.product_three_exact_cover_periodic`
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanSixCellResidue](KhetanSixCellResidue.md)
