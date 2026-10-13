# Leaf Existence in Sparse Matching-Cone-Saturated Graphs

## Abstract

Every finite maximal H-free graph of order at least twenty with at most order plus five edges has a vertex of degree one, for the cone H over three disjoint edges and an isolated vertex.

**Theorem 1.1 (A Sparse Saturated Host Has a Leaf).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] ((\mathrm{Maximal}\left(\mathrm{Free}\left(H\right), G\right)) \land ((20 \le \mathrm{FintypeCard}\left(V\right)) \land (\mathrm{card}\left(\mathrm{edgeFinset}\left(G\right)\right) \le \mathrm{FintypeCard}\left(V\right) + 5))) \Rightarrow (\exists v \in V,\; \mathrm{degree}\left(G, v\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafExistence.exists_degree_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is the existing eight-vertex graph MatchingConeLeafUniversality.H: its center has seven required neighbors, its pendant has one, and each of the six matching endpoints has two. Copies are injective adjacency-preserving maps, with extra host edges allowed. Maximal H-freeness means that every missing edge creates such a copy on the original vertex set.

A new copy must use the added edge as a required edge. If an isolated vertex v is joined to w, the degree bound in the enlarged graph forces v to occupy the pendant role and w the center. The six matching endpoints give six distinct old neighbors of w. This holds for every w other than v; the degree sum then contradicts the order and edge bounds. Thus there are no isolated vertices.

Suppose there is no leaf. Every vertex has degree at least two. Partition the same original host into C, the vertices of degree at least six, and L, the remaining vertices. The degree sum and edge bound give |C| <= 2 and sum over C of degree <= 2|C|+10, while |L| >= 18. Each x in L has degree at most five, so it has a distinct nonneighbor y in L. In a copy created by xy, neither endpoint can be the center: each enlarged degree is at most six. The center therefore has all seven required spokes in the old host, belongs to C, and is adjacent to x. Hence L lies in the union of the old neighbor sets of C. Counting that union by the sum of its set sizes gives |L| <= sum over C of degree. Consequently the host order is at most 10+3|C| <= 16, a contradiction.

The result preserves every finite original host, including disconnected and nonextremal hosts. It assumes neither exact edge count, connectivity, a universal vertex, nor an existing leaf. It is a structural implication, not a saturation-number equality, a sharp order cutoff, or a resolution of the general matching-cone problem. The finite role-degree calculations are consumed inside this unbounded structural proof; utility is none. The new inference is the saturation-forced old-host center incidence, which is used in the final counting contradiction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafExistence.exists_degree_one`
- Dependency: [D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality](MatchingConeLeafUniversality.md)
