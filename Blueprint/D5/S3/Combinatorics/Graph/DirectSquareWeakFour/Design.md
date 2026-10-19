# A sufficient incidence criterion and its assembly laws

## Abstract

A sufficient incidence criterion and its assembly laws

These criteria concern an incidence graph, not a disjoint union decomposition of the actual direct-product graph. Their separation consequence includes pairs with coordinates in different incidence blocks.

**Definition 1.1 (Sparse incidence criterion).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.Good`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.Good` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite bipartite incidence set is Good when every row and column degree is at least two, every simple three-edge path has endpoint degree total at least nine, and no rectangle has all four corners selected.

**Theorem 1.2 (All-pair sufficiency).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_resolves`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_resolves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order at least three, every Good incidence set is an actual weak-four landmark set. Shared-coordinate pairs use minimum degree two. A rectangle with at most two selected corners uses total degree at least eight; three corners use the path degree bound nine; four corners are excluded.

**Theorem 1.3 (Disjoint incidence union).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_join`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary coordinate types with decidable equality, the disjoint incidence union of two Good sets is Good. Every three-edge path and every four-cycle lies entirely in one of the two blocks. Degrees are preserved by the original union counting lemmas.

**Theorem 1.4 (Coordinate relabeling).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_map`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary equivalences of the two coordinate parts, mapping a Good incidence set along their product preserves all four conditions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.Good`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_join`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_map`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.good_resolves`
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core](Core.md)
- Dependency: [D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension](../HammingWeakTwoMetricDimension.md)
