# Shortest distances and weak-four separation in direct squares

## Abstract

Shortest distances and weak-four separation in direct squares

Vertices are ordered pairs of labels. Adjacency requires both coordinates to differ. The metric is the minimum length of an actual walk in this graph. The source is Farhan, Kuziak and Yero, arXiv:2605.22307v1, Proposition 2.2. The introductory definition omits the word distinct; its intended restriction is explicit in Proposition 2.2. Including a self-pair would give separation zero for every landmark set.

**Definition 1.1 (Direct-product adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, graph n is the finite simple graph on Fin n times Fin n in which vertices are adjacent exactly when both coordinates differ.

**Definition 1.2 (Coordinate distance expression).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.coordDist`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.coordDist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any two coordinate types with decidable equality, coordDist is zero at equal pairs, one when both coordinates differ, and two otherwise.

**Theorem 1.3 (Actual shortest distances).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.distance_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.distance_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least three, the actual shortest-walk distance equals coordDist for every pair of vertices. A nonadjacent distinct pair has a common neighbor by choosing a third row and a third column. No assumed metric is used.

**Theorem 1.4 (Connectedness).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least three the actual direct-product graph is connected. Thus its natural graph distance never takes the disconnected junk value.

**Definition 1.5 (Landmark separation).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite landmark set S and pair x,y, delta S x y is the sum over w in S of Nat.dist between the actual graph distances from x and y to w.

**Definition 1.6 (All distinct pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.IsWeakFour`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.IsWeakFour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A landmark set is weak four-resolving exactly when delta is at least four for every distinct pair of actual graph vertices.

**Definition 1.7 (Least feasible cardinality).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.wdim`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.wdim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, wdim n is the natural infimum of the achievable finite weak-four landmark cardinalities. At n at least four, the universal construction supplies a feasible set and the exact theorem proves that the infimum is an attained least cardinality.

**Theorem 1.8 (Shared-row identity).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_same_row`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_same_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least three, a row i and distinct columns j,jprime, separation equals the sum of their two column landmark degrees plus the membership indicators of the two compared vertices.

**Theorem 1.9 (Shared-column identity).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_same_col`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_same_col` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least three, a column j and distinct rows i,iprime, separation equals the sum of their two row landmark degrees plus the membership indicators of the compared vertices.

**Theorem 1.10 (Rectangle identity).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_rectangle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct rows i,iprime and distinct columns j,jprime, add the membership indicators of the compared diagonal vertices and twice those of the crossed corners to their separation. The result is the sum of the four row and column degrees. This identity follows by summing the contribution of each landmark.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.IsWeakFour`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.coordDist`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_rectangle`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_same_col`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.delta_same_row`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.distance_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.wdim`
- Dependency: [D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore](../HammingWeakTwoMetricDimensionCore.md)
