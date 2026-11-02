# Sparsity and tight-set closure

## Abstract

Finite simple graph counts, tight subsets, and exact Henneberg operations over arbitrary vertex types.

**Definition 1.1 (Edges induced by a vertex set).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.edgesIn`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/SparseSets.edgesIn` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every vertex type V, graph G and set S of vertices, edgesIn G S consists of the actual edges of G whose two endpoints lie in S. The map induced by subtype inclusion identifies it bijectively with the edge set of G induced on S.

**Definition 1.2 (Additive sparsity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsSparse`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsSparse` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph G and natural numbers k and ell, sparsity requires e(s)+ell <= k card(s) for every finite vertex set s for which ell <= k card(s). The additive convention avoids truncated natural subtraction.

**Definition 1.3 (Global tightness).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsTight`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsTight` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph G and natural k and ell, tightness combines sparsity with card(E(G))+ell=k card(V). Nat.card allows a universe-polymorphic statement; the constructions use finite V.

**Definition 1.4 (Local tightness).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsTightOn`

*Formalization.* `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsTightOn` (`✓ std3`).

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every graph G, natural k and ell and finite vertex set s, local tightness is the equality e(s)+ell=k card(s).

**Theorem 1.5 (A positive low-degree vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.exists_one_le_degree_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SparseSets.exists_one_le_degree_le_three` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite graph G that is (2,3)-sparse and has an edge, some vertex has degree between one and three. Restrict the degree sum to the vertices of positive degree. Every edge has both endpoints there. If all their degrees were at least four, handshake and sparsity on that same set would contradict each other.

**Theorem 1.6 (A nonadjacent neighbor pair).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.exists_nonadj_among_three_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SparseSets.exists_nonadj_among_three_neighbors` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

In a finite (2,3)-sparse graph, three distinct neighbors of any vertex cannot all be mutually adjacent. The four-vertex induced set would have six edges, exceeding its permitted five.

**Theorem 1.7 (Union and intersection of tight sets).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.union_inter`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SparseSets.union_inter` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For arbitrary k and ell and two tight finite sets s and t in a finite sparse graph, if ell <= k card(s intersection t), both the union and intersection are tight. Supermodularity of actual induced-edge counts and the cardinality identity squeeze the two sparsity inequalities simultaneously.

**Theorem 1.8 (Tight union with extra edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.union_with_bonus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SparseSets.union_with_bonus` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For arbitrary k and ell and a finite (k,ell)-sparse graph G, tight sets S and T have tight union if a set F of actual edges in their union is disjoint from the edges internal to S or T and its size closes the intersection deficit: e(S intersection T)+ell <= card(F)+k card(S intersection T). The proof counts the disjoint extra edges before applying sparsity.

**Theorem 1.9 (Tight extension by one vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/SparseSets.insert_vertex_with_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/SparseSets.insert_vertex_with_edges` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For arbitrary sparse G and tight finite S, let w lie outside S. If F consists of actual edges in S union {w}, disjoint from the edges internal to S, and k <= card(F), then S union {w} is tight. The edge-count lower bound and sparsity upper bound coincide.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsSparse`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsTight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.IsTightOn`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.edgesIn`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.exists_nonadj_among_three_neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.exists_one_le_degree_le_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.insert_vertex_with_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.union_inter`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/SparseSets.union_with_bonus`
