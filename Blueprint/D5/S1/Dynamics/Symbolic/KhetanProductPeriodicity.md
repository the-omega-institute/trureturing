# Product exact-cover bridge at the six-cell boundary

## Abstract

Exact-cover product fibres feed the six-cell residue dichotomy.

This module isolates the two-dimensional bridge for the product tile `{0,1} × {0,b,c}`. The one-dimensional theorem `three_point_tiling_residue` is an explicit hypothesis of the bridge. It is the unresolved Newman/Fourier input and is not proved or hidden here. Given that input, the exact-cover window forces adjacent columns to be disjoint and to form a residue-labelled XOR partition, after which `three_residue_column_dichotomy` supplies the horizontal/vertical period alternative.

**Definition 1.1 (Indicator of a column anchor).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.anchorBit`

*Formalization.* Repository-derived definition.

*Commentary.*

`anchorBit(T,x,y)` is the natural-number indicator of membership of `(x,y)` in the anchor set `T`. It expresses exact coverage as a sum of zero-one contributions.

**Definition 1.2 (One-dimensional three-point window count).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.oneDWindowCount`

*Formalization.* Repository-derived definition.

*Commentary.*

`oneDWindowCount(S,b,c,y)` sums the indicators of `S` at the three translated sites `y`, `y-b`, and `y-c`. The separate `three_point_tiling_residue` input consumes the assertion that this count is exactly one at every `y`.

**Definition 1.3 (Two-column product window count).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.productWindowCount`

*Formalization.* Repository-derived definition.

*Commentary.*

`productWindowCount(T,b,c,x,y)` sums the six possible anchors from columns `x-1` and `x` at vertical offsets `0`, `b`, and `c`. The hypothesis `productWindowCount = 1` is the exact unique-cover condition for the product tile.

**Theorem 1.4 (Exact-cover product fibres force a period).**

Lean statement: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.product_three_exact_cover_periodic`

*Formalization status.* Draft interface; scoped Lean verification is pending.

*Statement boundary.* The theorem assumes nonzero, distinct, coprime `b,c`, an explicit one-dimensional `three_point_tiling_residue` theorem for every predicate with exact three-point window count, and the two-column exact-cover equation. It derives adjacent-column disjointness and the residue/XOR hypotheses, then invokes `KhetanSixCellResidue.three_residue_column_dichotomy`.

*Commentary.*

The conclusion is the conditional product branch:

\[
\bigl(\forall x,y,\ T(x+2,y)\leftrightarrow T(x,y)\bigr)
\;\lor\;
\bigl(\forall x,y,\ T(x,y+3)\leftrightarrow T(x,y)\bigr).
\]

The one-dimensional rigidity and orbit-closure extraction remain separate obligations. This bridge therefore does not claim a resolution of the full six-cell open problem.

## References

- Dependency: `D5/S1/Dynamics/Symbolic/KhetanSixCellResidue.three_residue_column_dichotomy`
- Explicit unresolved input: `three_point_tiling_residue` (supplied as a theorem argument)
- Draft truth anchor: `D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.product_three_exact_cover_periodic`
