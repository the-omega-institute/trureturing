# The Catalan functional on finite linear forests

## Abstract

The alternating Catalan sum over all actual independent subsets of every finite acyclic graph of maximum degree two is nonnegative at every parameter at least its full vertex count.

**Theorem 1.1 (All vertices and all legal parameters).**

$$\forall V \in \mathrm{Type},\; \left(\operatorname{Fintype}\left(V\right) \land \operatorname{DecidableEq}\left(V\right)\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right) \Rightarrow \left(\forall m \in \mathrm{Nat},\; \left(\operatorname{IsAcyclic}\left(G\right) \land \left(\left(\forall v \in V,\; \operatorname{degree}\left(G, v\right) \le 2\right) \land \operatorname{card}\left(V\right) \le m\right)\right) \Rightarrow 0 \le \operatorname{phi}\left(G, \operatorname{univ}\left(V\right), m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan.finite_forest_phi_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any finite vertex type with decidable equality, and let G be any simple graph on V with decidable adjacency. Assume that G is acyclic and that every vertex has degree at most two. For every natural m at least the cardinality of V, the integer phi(G,univ,m) is nonnegative. Here phi is PathCatalanFunctional.phi: it sums (-1) to card(S) times Catalan(m-card(S)) over all actual independent subsets S of the full vertex set. Empty graphs, arbitrary isolated vertices, arbitrarily many components and the boundary m=card(V) are included.

A longest simple path in a connected component contains every vertex. An edge leaving an endpoint would extend it; an edge leaving an interior vertex would give three distinct neighbors. The Hamiltonian vertex enumeration identifies the path graph with a spanning subgraph, and maximal acyclicity excludes additional edges. Induction over the remaining actual vertices concatenates these component enumerations into a bijection from the full vertex type to a finite interval, carrying every original edge to consecutive indices.

For two distinct nonadjacent vertices u and v in a finite domain W, write N_u and N_v for the respective closed-neighborhood complements within W. The independent-partition deletion identity, applied at u and then at v inside N_u, gives P_G=P_(G+uv)+w(u)w(v)P_(G on N_u intersect N_v). The added edge does not change adjacency on a domain omitting an endpoint. With each activity equal to -X, multiply by the integer Catalan series and take coefficient m. When m is at least card(W), this yields phi(G,W,m)=phi(G+uv,W,m)+phi(G,N_u intersect N_v,m-2). The residual domain has at most card(W)-2 vertices.

Induct first on the full actual vertex count and then on the number of missing edges in the spanning path. The added-edge term reduces the missing-edge count; the residual term is an actual induced forest on fewer vertices and has a legal shifted parameter. At the complete path, the configuration-preserving vertex bijection transports the functional directly to PathCatalanFunctional.path_phi_nonnegative. Its path recurrence and generating-series identity are reused through that theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan.finite_forest_phi_nonnegative`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional](PathCatalanFunctional.md)
