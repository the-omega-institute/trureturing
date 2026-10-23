# Separation and capacity absorption

## Abstract

Distances between connected zero-capacity leaves in the original multigraph give both signed and rational capacity absorption bounds.

**Definition 1.1 (Original multigraph adjacency).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall src \in E \Rightarrow V,\; \forall dst \in E \Rightarrow V,\; \forall v \in V,\; \forall t \in V,\; \operatorname{Adj}\left(\operatorname{originalGraph}\left(src, dst\right), v, t\right) \Leftrightarrow \left(v \ne t \land \left(\left(\exists e \in E,\; \operatorname{apply}\left(src, e\right) = v \land \operatorname{apply}\left(dst, e\right) = t\right) \lor \left(\exists e \in E,\; \operatorname{apply}\left(src, e\right) = t \land \operatorname{apply}\left(dst, e\right) = v\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.originalGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let V and E be arbitrary finite types, with incidence maps src,dst:E to V. Each e is an edge identity, including when several identities have the same endpoints. The original graph joins distinct vertices precisely when an edge identity has those endpoints in either order. Its extended distance is the length of a shortest walk and is infinite for disconnected pairs. Collapsing parallel adjacency does not change this distance: every adjacent step uses one original edge. Parallel edges remain distinct in the incidence degree and in C, the cardinality of E.

**Theorem 1.2 (Absorption from the distance between leaves).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)], [\operatorname{Fintype}\left(E\right)], [\operatorname{DecidableEq}\left(V\right)], \forall src \in E \Rightarrow V,\; \forall dst \in E \Rightarrow V,\; \forall r \in V \Rightarrow \mathrm{Nat},\; \forall K \in \mathrm{Nat},\; \left(\left(\forall e \in E,\; \operatorname{apply}\left(src, e\right) \ne \operatorname{apply}\left(dst, e\right)\right) \land \left(\left(\forall v \in V,\; \operatorname{apply}\left(r, v\right) = 0 \Rightarrow \operatorname{degree}\left(src, dst, v\right) \le 1\right) \land \left(\left(\forall v \in V,\; 1 \le \operatorname{apply}\left(r, v\right) \Rightarrow \operatorname{degree}\left(src, dst, v\right) \le 2 \cdot \operatorname{apply}\left(r, v\right)\right) \land \left(\left(\forall e \in E,\; \neg (\operatorname{Leaf}\left(src, dst, r, \operatorname{apply}\left(src, e\right)\right) \land \operatorname{Leaf}\left(src, dst, r, \operatorname{apply}\left(dst, e\right)\right))\right) \land \operatorname{card}\left(\operatorname{leafVertices}\left(src, dst, r\right)\right) \le K\right)\right)\right)\right) \Rightarrow \left(\left(\forall d \in \mathrm{Nat},\; \left(2 \le d \land \left(\forall v \in V,\; \forall t \in V,\; \left(\operatorname{Leaf}\left(src, dst, r, v\right) \land \left(\operatorname{Leaf}\left(src, dst, r, t\right) \land v \ne t\right)\right) \Rightarrow \left(\operatorname{Reachable}\left(\operatorname{originalGraph}\left(src, dst\right), v, t\right) \Rightarrow d \le \operatorname{edist}\left(\operatorname{originalGraph}\left(src, dst\right), v, t\right)\right)\right)\right) \Rightarrow \left(\left(d + 1\right) \cdot \left(\operatorname{card}\left(E\right) - \operatorname{sum}\left(r\right)\right) \le \operatorname{sum}\left(r\right) + K \land \frac{d + 1}{d + 2} \cdot \left(\operatorname{card}\left(E\right) + K\right) \le \operatorname{sum}\left(r\right) + K\right)\right) \land \left(\left(\forall v \in V,\; \forall t \in V,\; \left(\operatorname{Leaf}\left(src, dst, r, v\right) \land \left(\operatorname{Leaf}\left(src, dst, r, t\right) \land v \ne t\right)\right) \Rightarrow \neg (\operatorname{Reachable}\left(\operatorname{originalGraph}\left(src, dst\right), v, t\right))\right) \Rightarrow \operatorname{card}\left(E\right) - \operatorname{sum}\left(r\right) \le 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.actual_capacity_port_separation_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maps src and dst have no loops. Capacities r:V to Nat satisfy degree(v) at most one when r(v)=0, and degree(v) at most 2r(v) when r(v)>0. Here degree counts incidences (e,false) and (e,true). A leaf is a vertex of capacity zero and degree one. No edge joins two such leaves. The natural number K is at least the number ell of leaf vertices. Set R=sum_v r(v), q=C−R, D=R+K and M=C+K. The signed quantities q,D are interpreted in Int; the fractional inequality is in Rat. In the formula, sum(r) denotes the sum over all vertices, and integer or rational casts are determined by the inequality in which they occur.

For every natural d at least two, assume that each pair of distinct connected leaves has original graph distance at least d. Then D is at least (d+1)q, and ((d+1)/(d+2))M is at most D. Separately, if no two distinct leaves are connected, q is nonpositive. The second conclusion does not require choosing d or assuming a distance bound. Reachable and edist in the formula refer to originalGraph(src,dst), so disconnected pairs impose no finite-distance condition.

Each positive-capacity vertex has exactly 2r(v) real and slack ports. A perfect matching on this even fiber supplies its local pairs. Zero-capacity vertices have only a single real leaf port or no ports. Combining the fiber matchings gives a base-preserving involution fixing exactly the leaf ports. Thus no routing is an additional hypothesis.

Along any path of the port graph, a local pairing step preserves the original vertex and a real-edge step changes it along one original edge. Induction on the port walk and the graph-distance triangle inequality bound the distance between its bases by the number of real edges, with no charge for local steps. A component with two leaf ports has a terminal path whose real-edge count is exactly its component length. Its endpoints have distinct bases, because a degree-one leaf has only one real port. They are therefore distinct connected original leaves at distance at most that component length.

The terminal counts give ell=2a+c and q=a−b, where a,b,c count LL, HH and LH components. Separation forces every LL component to contain at least d actual edges. Counting distinct edge identities by their port components gives C at least da, and K is at least 2a. Hence D=C−q+K is at least (d+1)q. This estimate holds for either sign of q. Substituting q=M−D and dividing by the positive d+2 gives the rational bound. If distinct leaves are never connected, there are no LL components; q=−b is nonpositive.

Empty vertex and edge carriers, isolated vertices, arbitrary positive capacities and parallel edges are included. The statement is about abstract capacity multigraphs. It does not assert that a rectangular residual graph satisfies any particular distance lower bound, nor that its signed deficit is always nonpositive.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.actual_capacity_port_separation_absorption`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.originalGraph`
- Dependency: [D5/S3/Combinatorics/Graph/CapacityPortParityAbsorption](../CapacityPortParityAbsorption.md)
