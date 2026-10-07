# Density from Hereditary Bipartite Cut Bounds

## Abstract

Hereditary bounds on bipartite cuts force a four-coloring and bound a loopless multigraph's edge count by three halves of its vertex count.

Let V be a finite set of vertices and E a finite set of indexed edges. Each edge e has two different endpoints l(e) and r(e) in the ambient vertex type. The coloring result permits endpoints outside V; the density result requires all endpoints in V. Different edge indices may have the same endpoints, so parallel edges are counted with their multiplicity. For S contained in V, inside(E,l,r,S) consists of the edges with both endpoints in S. CutCap requires, for every S contained in V and every L contained in S, that the number of these edges crossing between L and S minus L is at most the cardinality of S. This condition applies to every induced vertex set; a bound only on cuts of V is a different hypothesis.

For a nonempty subset A contained in S, the number of cuts splitting A is 2 to the power |S| minus 2 to the power (|S|-|A|+1). The two omitted kinds of cuts put all of A on one side. In particular each internal edge crosses exactly half the cuts. The empty and full cuts contain no crossing edges, so averaging the hereditary cut bounds makes the edge count of every nonempty induced vertex set strictly less than twice its size.

**Theorem 1.1 (Constructing a Four-Coloring).**

$$\forall V \in \mathrm{Finset}\left(Vertex\right),\; \forall E \in \mathrm{Finset}\left(Edge\right),\; \forall l \in \mathrm{Function}\left(Edge, Vertex\right),\; \forall r \in \mathrm{Function}\left(Edge, Vertex\right),\; (\mathrm{DistinctEndpoints}\left(E, l, r\right) \land \mathrm{EveryNonemptyInducedSetHasFewerThanTwiceAsManyEdges}\left(V, E, l, r\right)) \Rightarrow (\exists c \in \mathrm{Function}\left(Vertex, \mathrm{Fin}\left(4\right)\right),\; \mathrm{ProperOnInternalEdges}\left(V, E, l, r, c\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity.four_coloring_of_sparse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every nonempty S contained in V induces fewer than 2|S| edges, and every edge has different endpoints. There is a map from the vertex type to Fin(4) giving different colors to the endpoints of every edge inside V. No coloring condition is imposed on edges with an endpoint outside V. The degree sum counts each internal edge twice, so every nonempty induced vertex set has a vertex incident to at most three edges. Delete that vertex, color the remaining vertices by induction, then restore it with a color missing from its neighbors.

**Theorem 1.2 (The Three-Halves Density Bound).**

$$\forall V \in \mathrm{Finset}\left(Vertex\right),\; \forall E \in \mathrm{Finset}\left(Edge\right),\; \forall l \in \mathrm{Function}\left(Edge, Vertex\right),\; \forall r \in \mathrm{Function}\left(Edge, Vertex\right),\; (\mathrm{DistinctEndpoints}\left(E, l, r\right) \land \left(\mathrm{EndpointsIn}\left(V, E, l, r\right) \land \mathrm{CutCap}\left(V, E, l, r\right)\right)) \Rightarrow (2 \cdot \mathrm{card}\left(E\right) \le 3 \cdot \mathrm{card}\left(V\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity.bipartite_pseudoforest_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under CutCap, with different endpoints and all endpoints in V, twice the number of indexed edges is at most three times the number of vertices. Construct the four-coloring above and use the three ways to divide its four color classes into two pairs. Every edge crosses exactly two of the three resulting cuts. Each cut has at most |V| edges, which gives the asserted inequality. Empty vertex and edge sets are included. This is a finite graph statement; applying it to congruence classes requires a separate proof of the hereditary cut condition.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity.bipartite_pseudoforest_density`
- Truth anchor: `D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity.four_coloring_of_sparse`
