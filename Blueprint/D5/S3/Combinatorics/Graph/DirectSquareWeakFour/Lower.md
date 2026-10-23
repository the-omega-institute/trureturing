# Necessary incidence restrictions for weak-four landmarks

## Abstract

Necessary incidence restrictions for weak-four landmarks

The incidence graph has separate row and column vertices and one edge for each landmark. It is distinct from the ambient direct-product graph.

**Theorem 1.1 (Necessary row pair bound).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.row_pair_min`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.row_pair_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least four, every two distinct rows of a weak-four set have total landmark degree at least four. If their total degree were at most three, a column outside both supports would give a pair separated by at most three.

**Theorem 1.2 (Necessary column pair bound).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.col_pair_min`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.col_pair_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least four, every two distinct columns of a weak-four set have total landmark degree at least four, by the transposed support argument.

**Theorem 1.3 (Minimum incidence degree).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.minimum_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.minimum_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least four, a weak-four landmark set with fewer than 3n minus 2 landmarks has every row and column degree at least two. A degree-zero row forces all other degrees at least four; a degree-one row forces all others at least three. The column argument is identical in its parameters.

**Definition 1.4 (Bipartite incidence graph).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.incidence`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a landmark set S, incidence S is the simple graph on the disjoint union of row and column labels, with edge between row i and column j exactly when the pair belongs to S.

**Theorem 1.5 (Exact incidence degrees).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.incidence_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.incidence_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every order, the incidence degree of a row label equals its row landmark cardinality, and the degree of a column label equals its column landmark cardinality.

**Theorem 1.6 (Forbidden low path).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.no_low_rectangle_path`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.no_low_rectangle_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A weak-four set at order at least four cannot contain the three edges of a four-vertex incidence path when all four endpoint degrees are two. The crossed product pair then has separation at most three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.col_pair_min`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.incidence`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.incidence_degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.minimum_degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.no_low_rectangle_path`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.row_pair_min`
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core](Core.md)
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount](LowDegreeCount.md)
