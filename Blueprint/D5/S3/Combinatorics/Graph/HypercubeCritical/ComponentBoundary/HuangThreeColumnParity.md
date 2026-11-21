# Parity weights of three cube columns

## Abstract

Parity weights of three cube columns

Problem 2 in Section 7 of Hong, Wu and Xia's Graph Sensitivity of Cartesian Products with Matched Bridges asks whether the two-neighbor sensitivity of the nine-cube is 3 or 4. The 18+3 folded case has three minority columns on a common set of empty rows. The binary weight bound applies when each of these columns has exactly four retained neighbors. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Definition 1.1 (Weight of a selected set of columns).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity.cubeColumnParityWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity.cubeColumnParityWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any cube dimension, each vertex is a finite set of coordinates. Given a finite row set and three distinct centers indexed by 0, 1 and 2, the support of a column is the set of rows differing from that column's center in exactly one coordinate. The parity weight of a subset of the indices is the size of the symmetric difference of the selected supports, with empty symmetric difference equal to the empty set.

**Theorem 1.2 (Every nonempty selection has even weight from four through twelve).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity.cube_column_parity_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity.cube_column_parity_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the support of each of the three columns has exactly four rows on the common row set. For every nonempty subset of the three column indices, the parity weight belongs to {4, 6, 8, 10, 12}. Each single column has weight four. Two distinct centers have at most two common neighbors, so the symmetric difference of two supports has even size at least four.

If every pair of full neighborhoods intersects, translate the first center to the empty set by symmetric difference. The other centers become two-element sets whose symmetric difference has size two. A coordinate they share gives a neighbor of all three centers in the full cube. For each center, the overlaps with the other two neighborhoods therefore cover at most three neighbors. Each retained support supplies a distinct row private to that column, yielding at least three rows in the symmetric difference. If two full neighborhoods are disjoint, each of their retained supports contributes at least two private rows because the third neighborhood can cover at most two of its rows.

The symmetric difference of two sets has cardinality equal to the sum of their cardinalities minus twice their intersection size. Applying this identity twice shows that the three-column weight is even and at most twelve. Thus the three private rows in the pairwise-intersecting case already force weight at least four. In the folded axial equation this bound constrains any nonzero lowest-order binary syndrome obtained by reducing a normalized integral column combination modulo two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity.cubeColumnParityWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity.cube_column_parity_weight`
