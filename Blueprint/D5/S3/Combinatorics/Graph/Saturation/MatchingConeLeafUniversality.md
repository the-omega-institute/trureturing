# Leaf Neighbors in Sparse Matching-Cone-Saturated Graphs

## Abstract

A leaf's neighbor is universal in every finite maximal H-free graph with at most order plus five edges, where H is the cone over three disjoint edges and an isolated vertex.

**Definition 1.1 (The Eight-Vertex Matching Cone).**

$$H = \mathrm{Join}\left(\mathrm{K}\left(1\right), \mathrm{DisjointUnion}\left(\mathrm{ThreeCopies}\left(\mathrm{K}\left(2\right)\right), \mathrm{K}\left(1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is Unit + (Unit + (Fin 3 x Bool)). Its left unit is the center, its right-left unit is the pendant, and (i,false),(i,true) are the endpoints of matching edge i. The seven center spokes and the three matching edges are precisely its ten required edges. SimpleGraph.Copy is an injective adjacency-preserving map; additional host edges are allowed.

**Theorem 1.2 (The Neighbor of a Leaf Is Universal).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] \forall u \in V,\; \forall v \in V,\; ((\mathrm{Maximal}\left(\mathrm{Free}\left(H\right), G\right)) \land ((\mathrm{card}\left(\mathrm{edgeFinset}\left(G\right)\right) \le \mathrm{FintypeCard}\left(V\right) + 5) \land ((\mathrm{degree}\left(G, u\right) = 1) \land (\mathrm{Adj}\left(G, u, v\right))))) \Rightarrow (\mathrm{IsUniversal}\left(G, v\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality.leaf_neighbor_isUniversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let B be the vertices other than v not adjacent to v. For x in B, the leaf u is distinct from x and ux is missing. Maximal H-freeness supplies a copy after ux is added. A required edge must use ux. In the enlarged graph u lies in no triangle: its only possible neighbors are v and x, which are nonadjacent. Every H role except the pendant lies in a triangle, so u is the pendant and x the center. All six endpoint spokes and all three matching edges are old. An old neighbor of x outside those six endpoints could replace the pendant and construct an old forbidden copy. Consequently each x in B has degree six.

Delete the edges incident to v and call the resulting graph D. Write k = |B| and r = |E(D)|. The original edge bound gives r <= k+6. The degree sum gives 6k <= 2r, hence k <= 3. If k >= 2, the incidence sets of two distinct B vertices each have six edges and overlap in at most one edge, giving 11 <= r <= 9. If k = 1, its six spokes and three distinct matching edges give 9 <= r <= 7. Thus B is empty. All counts refer to this same host graph and its actual edge deletion.

The quantifiers range over arbitrary finite host types. No order cutoff, connectivity, existence of a leaf, exact saturation value, or resolution of a broader saturation problem is asserted. This structural implication is a repository derivation using Mathlib's copy, maximality, leaf uniqueness, incidence and degree-sum interfaces.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality.H`
- Truth anchor: `D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafUniversality.leaf_neighbor_isUniversal`
