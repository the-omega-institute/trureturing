# Real planar rigidity and spanning Laman graphs

## Abstract

For every finite vertex type in every universe, a simple graph on at least two vertices admits a real planar placement with rigidity kernel dimension at most three exactly when it contains a spanning Laman subgraph.

**Theorem 1.1 (Independent rows give a spanning Laman subgraph).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/PlanarLaman.exists_isLaman_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarLaman.exists_isLaman_le` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite enumeration of V, graph G admitting a rigid planar placement, and card(V)>=2, there exists a graph H on the same V with H<=G and H.IsLaman. The ambient graph G may have more edges than H.

Start with the placement witnessing a kernel of dimension at most three. Openness permits a perturbation along the moment curve for which every vertex subset of size at least three affinely spans the plane. Rank-nullity gives rank at least 2 card(V)-3. Select exactly that many independent actual edge rows and form H from their underlying unordered pairs.

For every induced subset of H with two vertices, simplicity bounds its edge count by one. On any larger subset, velocity restriction factors its rows through the smaller rigidity map and preserves their independence. Independent translations and a rotation provide three kernel directions there. Rank-nullity gives the induced bound. The selected total edge count is exactly 2 card(V)-3, so H is Laman.

**Theorem 1.2 (The complete planar equivalence).**

$$\forall V \in Type,\; [\operatorname{Finite}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (2 \le \operatorname{card}\left(V\right)) \Rightarrow ((\exists p \in \operatorname{Framework}\left(V, 2\right),\; \operatorname{finrank}\left(\operatorname{ker}\left(\operatorname{RigidityMap}\left(G, p\right)\right)\right) \le 3) \Leftrightarrow (\exists H \in \operatorname{SimpleGraph}\left(V\right),\; (H \le G) \land ((\operatorname{edgeCount}\left(H\right) + 3 = 2 \cdot \operatorname{card}\left(V\right)) \land (\forall S \in \operatorname{Set}\left(V\right),\; (2 \le \operatorname{card}\left(S\right)) \Rightarrow (\operatorname{edgeCount}\left(\operatorname{induce}\left(H, S\right)\right) + 3 \le 2 \cdot \operatorname{card}\left(S\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/PlanarLaman.isGenericallyRigid_two_iff_exists_isLaman_le` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Here Framework(V,2) is the space of arbitrary maps from V to the real Euclidean plane. RigidityMap(G,p) sends a velocity x to the edge-indexed inner products of p(u)-p(v) with x(u)-x(v). The kernel and its dimension are over the real numbers. The displayed edge count counts unordered edges, card counts the finite vertex set, and induce(H,S) is the graph induced on S.

The source predicate IsGenericallyRigid means existence of such a placement. It does not require algebraic independence of coordinates or assert local, global, or rigidity at every placement. The witness in the endpoint has no injectivity premise. Neither G nor H is assumed planar, and the number of vertices has no upper bound.

The forward implication from a spanning Laman H uses strong induction and the two geometric Henneberg moves to construct a rigid placement of H. The two-vertex case uses K2. Adding the remaining G edges shrinks the kernel. The other implication uses independent edge rows and all induced-subset bounds as above. H has exactly the original vertex type, including any labels; no construction history is an input.

The Laman predicate combines total tightness with the finite-subset sparsity condition. On finite V, converting a vertex set to its finite set preserves cardinality and the induced edge count. Its eligible-subset condition 3<=2 card(S) is equivalent to card(S)>=2. Thus its two clauses are precisely those displayed, for every induced vertex subset.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarLaman.exists_isLaman_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/PlanarLaman.isGenericallyRigid_two_iff_exists_isLaman_le`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/PlanarForward](PlanarForward.md)
- Dependency: [D5/S3/Combinatorics/Graph/Laman/PlanarRows](PlanarRows.md)
