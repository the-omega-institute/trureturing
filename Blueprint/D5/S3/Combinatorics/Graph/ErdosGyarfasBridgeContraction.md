# Bridge Contraction in Bipartite Graphs

## Abstract

Identifying the endpoints of a bridge preserves proper two-colourings, minimum degree at least three, and the lengths of all cycles.

**Definition 1.1 (Identifying the endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction`

*Formalization.* `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a graph G on V and vertices u and v, the contracted graph has vertex type {x in V | x differs from v}. Distinct remaining vertices x and y are adjacent precisely when G joins x to y, when x=u and G joins v to y, or when y=u and G joins x to v. The edge joining u and v is discarded.

**Theorem 1.2 (A cycle stays on one side of a cut vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.cycle_side_confinement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.cycle_side_confinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be any simple graph on V, a a vertex, and S a predicate on V. Suppose every edge x-y with x and y different from a satisfies S(x) if and only if S(y). For every closed walk p that is a cycle, either every vertex in its support equals a or satisfies S, or every vertex in its support equals a or fails S. Rotate a cycle containing a to begin there; its interior is a path avoiding a.

**Theorem 1.3 (Two-colourability is preserved).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \forall v \in V,\; \operatorname{IsBridge}\left(G, \operatorname{Sym2}\left(u, v\right)\right) \Rightarrow \left(\operatorname{Colorable}\left(G, 2\right) \Rightarrow \operatorname{Colorable}\left(\operatorname{contraction}\left(G, u, v\right), 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction_colorable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the original colouring on the component of u after deletion of the bridge. Exchange the colours of u and v on all other components. The redirected edges then have distinct endpoint colours.

**Theorem 1.4 (Minimum degree is preserved).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \forall v \in V,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{IsBridge}\left(G, \operatorname{Sym2}\left(u, v\right)\right) \Rightarrow \left(\operatorname{Adj}\left(G, u, v\right) \Rightarrow \left(\left(\forall z \in V,\; 3 \le \operatorname{degree}\left(G, z\right)\right) \Rightarrow \left(\forall x \in \operatorname{ContractVertex}\left(v\right),\; 3 \le \operatorname{degree}\left(\operatorname{contraction}\left(G, u, v\right), x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction_min_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoints of a bridge have no common neighbour. Every other vertex retains its neighbours after the redirection, while the merged vertex has the disjoint union of the two endpoint neighbourhoods with the bridge endpoints omitted. Its degree is at least four.

**Theorem 1.5 (Cycles lift with unchanged length).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in V,\; \forall v \in V,\; u \ne v \Rightarrow \left(\operatorname{IsBridge}\left(G, \operatorname{Sym2}\left(u, v\right)\right) \Rightarrow \left(\forall w \in \operatorname{ContractVertex}\left(v\right),\; \forall p \in \operatorname{Walk}\left(\operatorname{contraction}\left(G, u, v\right), w, w\right),\; \operatorname{IsCycle}\left(p\right) \Rightarrow \left(\exists z \in V,\; \exists q \in \operatorname{Walk}\left(G, z, z\right),\; \operatorname{IsCycle}\left(q\right) \land \operatorname{length}\left(q\right) = \operatorname{length}\left(p\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction_cycle_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The merged vertex separates the two sides of the deleted bridge. A cycle lies wholly on one side together with that vertex. Inclusion lifts a cycle on the u side; replacing the merged vertex by v lifts a cycle on the other side. Both maps are injective on their respective sides.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction_colorable`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction_cycle_lift`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.contraction_min_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction.cycle_side_confinement`
