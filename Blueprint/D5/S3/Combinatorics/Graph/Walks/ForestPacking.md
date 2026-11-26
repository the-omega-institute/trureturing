# Packing and covering subtrees of a forest

## Abstract

A family of subtrees of one finite forest has a disjoint subfamily and a vertex transversal of equal cardinality.

**Theorem 1.1 (A vertex with at most one neighbor).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\operatorname{Nonempty}\left(V\right) \Rightarrow \left(\operatorname{IsAcyclic}\left(G\right) \Rightarrow \left(\exists x \in V,\; \operatorname{Subsingleton}\left(\operatorname{neighborSet}\left(G, x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ForestPacking.exists_leaf_of_finite_forest` (`✓ std3`). ∎

*Citation.* Mahdi Jafari (2026). *Packing subtrees of a forest*. URL: <https://github.com/mahdi-jfri/GraphMinor/blob/04a7046c000043c02c6a3351f4d7d9a4b24b2b34/GraphMinor/GM16/ForestPacking.lean>.

*Commentary.*

Let V be a finite nonempty type in any universe u, and let G be a simple graph on V. If G is acyclic, there exists x in V whose neighbor set is subsingleton. Isolated vertices are allowed, so the neighbor set need not be nonempty. No connectedness hypothesis is imposed.

Choose a simple path of greatest length. Every neighbor of its initial vertex already lies on the path, since a new neighbor would extend it. Acyclicity then identifies every such neighbor with the second vertex of the path. Thus any two neighbors are equal.

**Theorem 1.2 (Removing a leaf preserves a nonsingleton subtree).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall A \in \operatorname{Set}\left(V\right),\; \operatorname{IsSubtreeSet}\left(G, A\right) \Rightarrow \left(\forall x \in V,\; \operatorname{Subsingleton}\left(\operatorname{neighborSet}\left(G, x\right)\right) \Rightarrow \left(A \ne \operatorname{singleton}\left(x\right) \Rightarrow \operatorname{IsSubtreeSet}\left(\operatorname{induce}\left(G, \operatorname{compl}\left(\operatorname{singleton}\left(x\right)\right)\right), \operatorname{restrict}\left(A, \operatorname{compl}\left(\operatorname{singleton}\left(x\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ForestPacking.remove_leaf` (`✓ std3`). ∎

*Citation.* Mahdi Jafari (2026). *Packing subtrees of a forest*. URL: <https://github.com/mahdi-jfri/GraphMinor/blob/04a7046c000043c02c6a3351f4d7d9a4b24b2b34/GraphMinor/GM16/ForestPacking.lean>.

*Commentary.*

Let V be any type in universe u, G a simple graph on V, A a vertex set, and x a vertex. IsSubtreeSet(G,A) means that A is nonempty and every two vertices of A are joined by an actual simple G-path whose entire vertex support lies in A. If the neighbor set of x is subsingleton and A is not the singleton containing x, then the set of vertices of A in the complement of that singleton is an IsSubtreeSet in the induced graph. In the formula, restrict(A, complement(singleton(x))) denotes the set of subtype vertices a with a.val in A. Neither finiteness nor acyclicity of G is a premise of this assertion.

Nonemptiness follows because a nonempty set unequal to the singleton leaf has a vertex different from that leaf. A simple path between two such vertices cannot pass through a vertex with at most one neighbor. Its induced walk on the complement remains a simple path and all its vertices remain in A.

**Theorem 1.3 (A nonsingleton connected set contains a neighbor).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall A \in \operatorname{Set}\left(V\right),\; \operatorname{IsSubtreeSet}\left(G, A\right) \Rightarrow \left(\forall x \in V,\; x \in A \Rightarrow \left(A \ne \operatorname{singleton}\left(x\right) \Rightarrow \left(\exists y \in V,\; y \in A \land \operatorname{Adj}\left(G, x, y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ForestPacking.exists_neighbor` (`✓ std3`). ∎

*Citation.* Mahdi Jafari (2026). *Packing subtrees of a forest*. URL: <https://github.com/mahdi-jfri/GraphMinor/blob/04a7046c000043c02c6a3351f4d7d9a4b24b2b34/GraphMinor/GM16/ForestPacking.lean>.

*Commentary.*

For an arbitrary vertex type V, simple graph G and IsSubtreeSet(G,A), if x belongs to A and A is not the singleton containing x, there exists y in A adjacent to x. The graph and its vertex type may be infinite, and x need not be a leaf.

Choose another vertex of A. A path inside A from x to that vertex is nonempty. Its second vertex belongs to A and is adjacent to x.

**Theorem 1.4 (Lifting disjointness across a deleted leaf).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall A \in \operatorname{Set}\left(V\right),\; \forall B \in \operatorname{Set}\left(V\right),\; \forall x \in V,\; \operatorname{IsSubtreeSet}\left(G, A\right) \Rightarrow \left(\operatorname{IsSubtreeSet}\left(G, B\right) \Rightarrow \left(\operatorname{Subsingleton}\left(\operatorname{neighborSet}\left(G, x\right)\right) \Rightarrow \left(A \ne \operatorname{singleton}\left(x\right) \Rightarrow \left(B \ne \operatorname{singleton}\left(x\right) \Rightarrow \left(\operatorname{Disjoint}\left(\operatorname{restrict}\left(A, \operatorname{compl}\left(\operatorname{singleton}\left(x\right)\right)\right), \operatorname{restrict}\left(B, \operatorname{compl}\left(\operatorname{singleton}\left(x\right)\right)\right)\right) \Rightarrow \operatorname{Disjoint}\left(A, B\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ForestPacking.disjoint_of_disjoint_remove_leaf` (`✓ std3`). ∎

*Citation.* Mahdi Jafari (2026). *Packing subtrees of a forest*. URL: <https://github.com/mahdi-jfri/GraphMinor/blob/04a7046c000043c02c6a3351f4d7d9a4b24b2b34/GraphMinor/GM16/ForestPacking.lean>.

*Commentary.*

For any vertex type V and simple graph G, let A and B be IsSubtreeSet vertex sets. Suppose x has a subsingleton neighbor set, neither A nor B is the singleton containing x, and their restrictions to the complement of that singleton are disjoint. Then the original sets A and B are disjoint. No finiteness or acyclicity premise is required.

A common vertex different from x contradicts disjointness of the restrictions. If x belongs to both original sets, the preceding neighbor result gives a neighbor in each set. The leaf hypothesis makes these neighbors equal, giving a common vertex different from x and the same contradiction.

**Theorem 1.5 (One packing and transversal with equal size).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall v \in \operatorname{Universe}\left(\right),\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall I \in \operatorname{Type}\left(v\right),\; \forall A \in I \to \operatorname{Set}\left(V\right),\; \operatorname{IsAcyclic}\left(G\right) \Rightarrow \left(\left(\forall i \in I,\; \operatorname{IsSubtreeSet}\left(G, \operatorname{A}\left(i\right)\right)\right) \Rightarrow \left(\exists J \in \operatorname{Finset}\left(I\right),\; \exists X \in \operatorname{Finset}\left(V\right),\; \operatorname{card}\left(X\right) = \operatorname{card}\left(J\right) \land \left(\left(\forall i \in I,\; i \in J \Rightarrow \left(\forall j \in I,\; j \in J \Rightarrow \left(i \ne j \Rightarrow \operatorname{Disjoint}\left(\operatorname{A}\left(i\right), \operatorname{A}\left(j\right)\right)\right)\right)\right) \land \left(\forall i \in I,\; \exists x \in V,\; x \in X \land x \in \operatorname{A}\left(i\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ForestPacking.forest_packing_cover` (`✓ std3`). ∎

*Citation.* Mahdi Jafari (2026). *Packing subtrees of a forest*. URL: <https://github.com/mahdi-jfri/GraphMinor/blob/04a7046c000043c02c6a3351f4d7d9a4b24b2b34/GraphMinor/GM16/ForestPacking.lean>.

*Commentary.*

For independent universes u and v, let V be a type in Type u with Finite(V), let I be any type in Type v, let G be a simple graph on V, and let A map I to Set(V). Assume G.IsAcyclic and IsSubtreeSet(G,A(i)) for every i. There exist J : Finset(I) and X : Finset(V) such that |X| = |J|, every two distinct indices in J have disjoint original sets, and for every i in I there exists x in X belonging to A(i). The same J and X satisfy the three conclusions in the same graph and original family.

Induct strongly on the number of host vertices. In a nonempty host choose a leaf x. If some family member equals the singleton containing x, select one such index and recurse on the other members that omit x in the graph with x deleted. Add the chosen index to the packing and x to the transversal; each cardinality increases by one. If no member is that singleton, delete x from every member and recurse. The removal result preserves every subtree, and the disjointness result lifts the packing to the original sets. Mapping the smaller transversal back to V preserves its size and covers every original member. In an empty host every nonempty family member is impossible, so both finite sets are empty.

The index type has no finiteness or nonemptiness assumption. Empty index types, repeated vertex sets, disconnected forests and isolated vertices are included. An empty host is included whenever the hypotheses are satisfiable. A leaf, a root, an order, a packing, a transversal and a cardinality bound are all absent from the premises. The result is an unweighted existence theorem; it gives no uniqueness, algorithmic complexity, weighted-cost or infinite-host conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ForestPacking.disjoint_of_disjoint_remove_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ForestPacking.exists_leaf_of_finite_forest`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ForestPacking.exists_neighbor`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ForestPacking.forest_packing_cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ForestPacking.remove_leaf`
