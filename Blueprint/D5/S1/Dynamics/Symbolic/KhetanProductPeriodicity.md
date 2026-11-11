# Product exact-cover bridge at the six-cell boundary

## Abstract

Exact-cover product fibres feed the six-cell residue dichotomy.

This module isolates the two-dimensional bridge for a product tile {0,1} × {0,b,c}, with distinct offsets and gcd(b,c)=1. The classical prime-three shift argument proves that every one-dimensional exact-cover complement is a single residue class modulo three. This classification is proved inside the module. The exact-cover window forces adjacent columns to be disjoint and to form a residue-labelled XOR partition, after which the existing three_residue_column_dichotomy supplies the horizontal/vertical period alternative.

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

oneDWindowCount(S,b,c,y) sums the indicators of S at the three translated sites y, y-b, and y-c. When this count is one at every integer and the offsets are primitive, the module proves that S is one residue class modulo three.

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

Assume b and c are nonzero, distinct, and coprime. If every two-column product window has count one, the theorem derives disjoint adjacent columns and proves a residue/XOR partition.

For each adjacent-column union, the indicator f satisfies f(y)+f(y-b)+f(y-c)=1. Combining this equation at six shifted sites with weights 1,2,2,1,2,1 yields a cubic identity modulo three. Its three diagonal terms are zero-one values, so they are equal; this gives periods 3b and 3c. Bézout gives period three, and summing the cover equation over the three residue classes shows that exactly one class is occupied.

The conclusion is exactly the existing residue dichotomy: either T(x+2,y) ↔ T(x,y) for all x,y, or T(x,y+3) ↔ T(x,y) for all x,y. This proves the product branch on the infinite lattice from exact coverage alone. It does not resolve the full six-cell orbit-closure problem: the periodizer and affine-coordinate reduction for an arbitrary full-span six-point tile remain separate obligations.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.anchorBit`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.oneDWindowCount`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.productWindowCount`
- Truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.product_three_exact_cover_periodic`
- Dependency: [D5/S1/Dynamics/Symbolic/KhetanSixCellResidue](KhetanSixCellResidue.md)
