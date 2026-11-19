# The even-radius extension of the small q-kernel bound is false

## Abstract

A bipartite digraph on 29 vertices needs seven centers at radius four, exceeding the six allowed by the proposed bound.

**Definition 1.1 (The proposed bound for even radii).**

$$claim \Leftrightarrow (\forall q \in \mathrm{Nat},\; (\operatorname{Even}\left(q\right) \land 4 \le q) \Rightarrow (\forall (V : Type) [\operatorname{Fintype}\left(V\right)], \forall G \in \operatorname{Digraph}\left(V\right),\; (\operatorname{Loopless}\left(G\right) \land \left(\operatorname{Bipartite}\left(G\right) \land \left(\operatorname{SourceFree}\left(G\right) \land \operatorname{HasOutBranching}\left(G\right)\right)\right)) \Rightarrow (\exists Q \in \operatorname{Finset}\left(V\right),\; \operatorname{Independent}\left(G, Q\right) \land \left(\operatorname{Covers}\left(G, q, Q\right) \land \left(q + 1\right) \cdot \operatorname{card}\left(Q\right) \le \operatorname{card}\left(V\right) + q + 1\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.claim` (`✓ std3`).

*Citation.* Irena Penev, Maya Stein, and Ana Trujillo-Negrete (2026). *Small q-kernels in digraphs*. DOI: [10.48550/arXiv.2608.00825](https://doi.org/10.48550/arXiv.2608.00825). URL: <https://arxiv.org/abs/2608.00825v1>.

*Commentary.*

The question immediately after Theorem 1.6 of arXiv:2608.00825v1 asks whether the theorem extends to even q. With the printed lower endpoint, this quantifies over every even natural q at least four. The graph ranges over every finite vertex type with a directed adjacency relation. At most one arc occurs in each ordered direction, and opposite arcs can coexist.

Loopless forbids adjacency from a vertex to itself. Bipartite asks for a Boolean coloring with different colors at the ends of every ambient arc, equivalent to bipartiteness of the underlying simple graph. SourceFree asks for an incoming ambient arc at every vertex. HasOutBranching asks for a subgraph on the entire vertex type whose directed paths from its root are unique, using the Mathlib arborescence structure.

Independent forbids every ambient arc between members of Q. Covers asks for each vertex to be reached from some member of Q along a directed path in G with distinct vertices and at most q arcs. Length zero is allowed. The multiplicative bound is obtained from the printed fractional bound by multiplying by the positive q + 1.

**Theorem 1.2 (The radius-four refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Irena Penev, Maya Stein, and Ana Trujillo-Negrete (2026). *Small q-kernels in digraphs*. DOI: [10.48550/arXiv.2608.00825](https://doi.org/10.48550/arXiv.2608.00825). URL: <https://arxiv.org/abs/2608.00825v1>.

*Commentary.*

Take the directed cycle 0 → 1 → 2 → 3 → 4 → 5 → 0 and the arc 0 → 6. The three branches are 6 → 7 → 8 → 9 → 10, 6 → 11 → 12 → 13 → 14 → 15 → 16 → 17 → 18 → 19, and 6 → 20 → 21 → 22 → 23 → 24 → 25 → 26 → 27 → 28. Add 15 → 6 and 24 → 6. Every vertex has an in-neighbor. Alternating colors on the cycle and along the branches gives a bipartition, since both return arcs start at odd depth. Deleting 5 → 0 and the two return arcs gives an out-arborescence rooted at 0.

Two centers on the directed six-cycle are compulsory. It has no incoming arc from outside, and one center reaches at most five cycle vertices within four arcs. If the hub 6 is absent, the demands 10, 14, 19, 23 and 28 have pairwise disjoint predecessor intervals after excluding 6. If the hub is present, the demands 15 and 19 can share only predecessor 15, which independence excludes because of 15 → 6. The demands 24 and 28 similarly cannot share 24. The two pairs require four branch centers in addition to the hub. Both cases force at least five centers outside the cycle.

The proof checks predecessor membership and disjointness by kernel reduction on the fixed graph. It then counts centers in an arbitrary cover using the disjoint cycle and branch parts. Seven centers imply 5|Q| at least 35, while the source bound on 29 vertices gives 5|Q| at most 34.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PenevEvenQKernelRefutation.result`
