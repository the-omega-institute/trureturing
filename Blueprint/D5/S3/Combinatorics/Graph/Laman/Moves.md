# Henneberg preservation and reconstruction

## Abstract

Finite simple graph counts, tight subsets, and exact Henneberg operations over arbitrary vertex types.

**Definition 1.1 (Laman counts).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.IsLaman`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Moves.IsLaman` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every simple graph, the Laman property is (2,3)-tightness: every eligible finite subset obeys its induced-edge bound and the total edge count meets it.

**Theorem 1.2 (Minimum degree in the nonbase case).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.two_le_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Moves.two_le_degree` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A Laman graph on at least three vertices has degree at least two at every vertex. Apply sparsity to the complement of that vertex and use the partition of all edges into incident and nonincident edges.

**Theorem 1.3 (The two-vertex base).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.eq_top_of_card_eq_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Moves.eq_top_of_card_eq_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A Laman graph on exactly two vertices is complete. Tightness gives one edge, and inclusion in the complete graph with the same finite edge count gives equality.

**Theorem 1.4 (K2 satisfies the counts).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.top_fin_two_isLaman`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Moves.top_fin_two_isLaman` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

The complete graph on Fin 2 is Laman. It has one edge, and the only eligible subset is the whole two-vertex set.

**Definition 1.5 (Type I adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.typeI`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Moves.typeI` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every G and old vertices a,b, the output lives on Option V. Two some-vertices are adjacent exactly when their old vertices were adjacent; none is adjacent to some u exactly when u=a or u=b; none has no loop. A legal move additionally requires a != b.

**Definition 1.6 (Type II adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.typeII`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Moves.typeII` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every G and old vertices a,b,c, two some-vertices remain adjacent exactly when they were adjacent and their unordered pair differs from {a,b}. The fresh none vertex is adjacent exactly to some a, some b and some c, and has no loop. A legal move requires the actual old edge ab and all three old vertices distinct.

**Theorem 1.7 (Type I preserves Laman counts).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.typeI_isLaman`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Moves.typeI_isLaman` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite Laman G and distinct old vertices a,b, its Type I extension is Laman. For each induced subset, separate old edges from its at most two fresh edges; subsets omitting the fresh vertex inherit the old bound directly. The total count increases by two edges and one vertex.

**Theorem 1.8 (Type II preserves every induced-subset bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.typeII_isLaman`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Moves.typeII_isLaman` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite Laman G, actual edge ab and third vertex c distinct from both endpoints, its Type II extension is Laman. For an induced subset, remove none to obtain its old part, subtract the bridge when present, and count the fresh incident edges. If all three neighbors occur, the deleted old edge supplies the required unit of slack. Otherwise there are at most two fresh edges; the one-vertex and empty old parts are handled separately. The proof covers every subset and does not assume planarity or placement.

**Definition 1.9 (Exact Type I reconstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.isoTypeIOfTwoNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Moves.isoTypeIOfTwoNeighbors` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

If the neighbors of v are exactly a and b, with both different from v, Option of the vertex-deletion subtype is isomorphic to the original graph. The equivalence sends the unique fresh none vertex to v and some w to its original old vertex; all four adjacency cases are checked.

**Definition 1.10 (Exact Type II reconstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.isoTypeIIOfThreeNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/Moves.isoTypeIIOfThreeNeighbors` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

If the neighbors of v are exactly a,b,c, none equals v, and a,b are not adjacent in the original graph, repair the deletion graph by adding ab. Applying Type II deletes exactly that bridge. The Option/subtype equivalence preserves every other old adjacency and gives precisely the original incident edges at v.

**Theorem 1.11 (A smaller Laman graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/Moves.exists_typeI_or_typeII_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/Moves.exists_typeI_or_typeII_reverse` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Every finite Laman graph on at least three vertices admits a Type I or Type II reverse to a Laman graph on the subtype excluding one vertex. Minimum degree excludes the pendant case. Type I tightness follows by reconstruction and reverse preservation; Type II tightness follows from the safe sparse repair, the actual bridge edge, and the exact edge count.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.IsLaman`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.eq_top_of_card_eq_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.exists_typeI_or_typeII_reverse`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.isoTypeIIOfThreeNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.isoTypeIOfTwoNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.top_fin_two_isLaman`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.two_le_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.typeI`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.typeII`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.typeII_isLaman`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/Moves.typeI_isLaman`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/SafeRepair](SafeRepair.md)
