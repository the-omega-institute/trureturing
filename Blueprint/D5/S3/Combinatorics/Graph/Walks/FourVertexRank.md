# Actual Perfect Matchings on Four Vertices

## Abstract

Actual perfect matchings on four vertices admit three pairings. Their supported pairs give the exact number of perfect-matching subgraphs.

Vertices are indexed by Fin 4, with indices 0, 1, 2, 3. The three partner maps exchange respectively the pairs 01 and 23, 02 and 13, and 03 and 12. A perfect matching is an actual SimpleGraph.Subgraph satisfying IsPerfectMatching; it includes every vertex and gives each vertex exactly one adjacent partner.

**Definition 1.1 (Three Partner Maps).**

$$\forall j \in \mathrm{Fin}\left(3\right),\; \forall i \in \mathrm{Fin}\left(4\right),\; \mathrm{mate}\left(j, i\right) = \mathrm{Entry}\left(\mathrm{PartnerTable}, j, i\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.mate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PartnerTable has rows (1,0,3,2), (2,3,0,1), and (3,2,1,0). Every row is an involution without a fixed vertex.

**Definition 1.2 (Actual Perfect-Matching Count).**

$$\forall H \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(4\right)\right),\; \mathrm{pmCount}\left(H\right) = \mathrm{card}\left(\mathrm{PerfectMatchingSubgraphs}\left(H\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.pmCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PerfectMatchingSubgraphs(H) is the subtype of all subgraphs M of H with M.IsPerfectMatching. Its cardinality is Nat.card of this finite type.

**Theorem 1.3 (Exact Matching Objects and Count).**

$$\forall H \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(4\right)\right),\; (\forall M \in \mathrm{Subgraph}\left(H\right),\; (\mathrm{IsPerfectMatching}\left(M\right)) \Leftrightarrow (\exists j \in \mathrm{Fin}\left(3\right),\; (\forall i \in \mathrm{Fin}\left(4\right),\; \mathrm{Adj}\left(H, i, \mathrm{mate}\left(j, i\right)\right)) \land (\forall i \in \mathrm{Fin}\left(4\right),\; \forall k \in \mathrm{Fin}\left(4\right),\; (\mathrm{Adj}\left(M, i, k\right)) \Leftrightarrow (\mathrm{mate}\left(j, i\right) = k)))) \land (\mathrm{pmCount}\left(H\right) = \mathrm{indicator}\left((\mathrm{Adj}\left(H, 0, 1\right)) \land (\mathrm{Adj}\left(H, 2, 3\right))\right)+\mathrm{indicator}\left((\mathrm{Adj}\left(H, 0, 2\right)) \land (\mathrm{Adj}\left(H, 1, 3\right))\right)+\mathrm{indicator}\left((\mathrm{Adj}\left(H, 0, 3\right)) \land (\mathrm{Adj}\left(H, 1, 2\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.actual_matching_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the unique partner of vertex 0. It is 1, 2, or 3. Symmetry fixes its partner as 0. The two remaining vertices must be paired with each other, because the already paired vertices cannot acquire a second partner. Conversely, each of the three pairings gives a perfect-matching subgraph exactly when both of its edges occur in H. The public equivalence ranges over every actual subgraph M of H: M is a perfect matching if and only if its adjacency relation is one of the three supported partner maps. Support means that H contains every prescribed partner edge. Because every vertex has a partner, these subgraphs also have the full vertex set; no isolated-vertex choices remain. The constructions form a bijection, so their supported indicators sum to the actual cardinality. Each indicator is 1 when its two edges occur and 0 otherwise.

The counting formula holds for every simple graph on these four vertices. The weighted and binary adjacency rank tables, the classification up to graph isomorphism, and the signed rank difference require further arguments.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.actual_matching_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.mate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.pmCount`
