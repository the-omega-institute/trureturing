# Trees and triple Helly intersections

## Abstract

Triple intersections of connected induced vertex sets characterize connected acyclic graphs on arbitrary vertex types.

**Theorem 1.1 (Three connected sets from any cycle).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall v \in V,\; \forall p \in \operatorname{Walk}\left(G, v, v\right),\; \operatorname{IsCycle}\left(p\right) \Rightarrow \left(\exists A \in \operatorname{Set}\left(V\right),\; \exists B \in \operatorname{Set}\left(V\right),\; \exists C \in \operatorname{Set}\left(V\right),\; \operatorname{Connected}\left(\operatorname{induce}\left(G, A\right)\right) \land \left(\operatorname{Connected}\left(\operatorname{induce}\left(G, B\right)\right) \land \left(\operatorname{Connected}\left(\operatorname{induce}\left(G, C\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{inter}\left(A, B\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{inter}\left(B, C\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{inter}\left(C, A\right)\right) \land \operatorname{inter}\left(\operatorname{inter}\left(A, B\right), C\right) = \operatorname{emptyset}\left(V\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/TripleHellyRecognition.exists_connected_triple_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u be any universe, V a type in Type u, G a simple undirected graph on V, v a vertex, and p a native G.Walk from v to v. If p.IsCycle, there exist vertex sets A, B and C such that all three induced graphs are connected, each of A intersect B, B intersect C and C intersect A is nonempty, and A intersect B intersect C is empty. Neither G nor its vertex type is required to be finite or connected.

Write the first two edges of the cycle as x-to-y and y-to-z, and let r be the remaining walk from z to x. A cycle has at least three edges. Set A equal to the pair containing x and y, B equal to the pair containing y and z, and C equal to the support of r. Adjacency makes the induced graphs on A and B connected, while the induced graph on the support of any walk is connected. This last fact does not require the walk to be a path.

The vertices y, z and x belong respectively to A intersect B, B intersect C and C intersect A. The cycle condition makes the support after its first vertex duplicate-free, so y does not belong to the support of r. Also x differs from z: equality would repeat the first edge in the opposite direction, contradicting the cycle's edge distinctness. Thus the only possible common vertex of A and B is y, and it is absent from C. This proves the empty triple intersection.

All three induced graphs use the edges of the original ambient graph. Chords and other extra ambient edges are permitted; they cannot destroy the exhibited connections or change the memberships of the three vertex sets. In a triangle the remaining walk is a single edge, and the same construction applies.

**Theorem 1.2 (Recognition among connected graphs).**

$$\forall u \in \operatorname{Universe}\left(\right),\; \forall V \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{Connected}\left(G\right) \Rightarrow \left(\operatorname{IsTree}\left(G\right) \Leftrightarrow \left(\forall A \in \operatorname{Set}\left(V\right),\; \forall B \in \operatorname{Set}\left(V\right),\; \forall C \in \operatorname{Set}\left(V\right),\; \left(\operatorname{Connected}\left(\operatorname{induce}\left(G, A\right)\right) \land \left(\operatorname{Connected}\left(\operatorname{induce}\left(G, B\right)\right) \land \left(\operatorname{Connected}\left(\operatorname{induce}\left(G, C\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{inter}\left(A, B\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{inter}\left(B, C\right)\right) \land \operatorname{Nonempty}\left(\operatorname{inter}\left(C, A\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{inter}\left(\operatorname{inter}\left(A, B\right), C\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/TripleHellyRecognition.isTree_iff_connected_triple_helly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every universe u, every V in Type u, every simple graph G on V and every proof of G.Connected, G.IsTree is equivalent to the following property. For all sets A, B and C of vertices, if each induced graph is connected and each of the three pair intersections is nonempty, then A intersect B intersect C is nonempty. The quantifiers allow repeated sets and an infinite ambient vertex type. Native Connected includes nonemptiness, and native IsTree consists of connectedness together with the absence of native cyclic walks.

For the forward implication, apply the finite-family subtree Helly theorem to the family indexed by Fin(3), with values A, B and C. The three off-diagonal intersections are given, their reverse orders follow by commutativity, and the diagonal intersections are nonempty because the sets already have pairwise intersections. Only this indexing family is finite. The ambient vertex type remains arbitrary.

For the reverse implication, take any actual closed walk and suppose it is a cycle. The preceding construction supplies A, B and C satisfying every premise of the triple property but having empty triple intersection. The asserted nonempty triple intersection is a contradiction. Hence every closed walk fails to be a cycle, which is exactly native IsAcyclic. Together with the assumed connectedness this yields native IsTree.

The forward implication uses SimpleGraph.IsTree.inter_nonempty_of_pairwise from SubtreeHelly, whose proof source and Apache attribution are recorded there and in its Library note. The cycle construction and the converse are derived here from native walk facts. No claim about literature priority is made. The characterization concerns three sets; it asserts neither an infinite-family intersection property nor an algorithmic bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/TripleHellyRecognition.exists_connected_triple_obstruction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/TripleHellyRecognition.isTree_iff_connected_triple_helly`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/SubtreeHelly](SubtreeHelly.md)
