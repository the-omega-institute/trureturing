# Prescribed graph subdivisions

## Abstract

Explicit fresh vertices, endpoint incidence and edge counts for prescribed triple subdivisions.

The original vertex type V and edge-index type E are arbitrary. Data D specifies distinct left and right endpoints and positive natural multiplicities k(e). No injectivity of the unordered endpoint pairs is assumed by this general construction. The concrete routing module supplies that property for its simple original graph.

**Definition 1.1 (The actual fresh vertices).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; \operatorname{Vertex}\left(D\right):\mathrm{Type}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Interior is the dependent sum of Fin (3 k(e)) over E. The sum tag distinguishes every old vertex from every fresh vertex, and the dependent edge tag distinguishes different routes. Interior index i denotes path position i+1.

**Definition 1.2 (Path positions and endpoints).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; \forall e \in E,\; \forall i \in \operatorname{Fin}\left(3 \cdot \operatorname{k}\left(D, e\right) + 2\right),\; \operatorname{pathVertex}\left(D, e, i\right):\operatorname{Vertex}\left(D\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.pathVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an edge e, positions are 0 through 3 k(e)+1. Position zero is the old left endpoint, the last position is the old right endpoint, and intermediate positions use the corresponding fresh tag. Thus each edge is replaced by a path of 3 k(e)+1 edges.

**Theorem 1.3 (Each prescribed path is simple).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; \forall e \in E,\; \operatorname{Injective}\left(\operatorname{pathVertex}\left(D, e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.pathVertex_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every e, distinct positions map to distinct actual vertices. Distinct endpoints, positivity and the explicit tags handle the endpoint and interior cases.

**Theorem 1.4 (Every oriented edge has a literal slot).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; \forall a \in \operatorname{Vertex}\left(D\right),\; \forall b \in \operatorname{Vertex}\left(D\right),\; \operatorname{Arc}\left(D, a, b\right) \Leftrightarrow \left(\exists s \in \operatorname{Slot}\left(D\right),\; \operatorname{edgePair}\left(D, s\right) = \operatorname{Pair}\left(a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.arc_iff_slot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all vertices a,b, Arc a b holds exactly when a slot s produces the ordered pair (a,b). A slot consists of e and an index from 0 through 3 k(e). The graph symmetrizes Arc; there are no extra edges between old vertices or different fresh routes.

**Theorem 1.5 (No duplicate unordered path edge).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; \operatorname{Injective}\left(\operatorname{edge}\left(D\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.edge_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Different slots produce different unordered edges. Reversing an oriented edge cannot identify two slots because Arc is asymmetric. Parallel original endpoint pairs cause no collision among the fresh path edges.

**Theorem 1.6 (Natural tags retain every actual vertex).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; \operatorname{Injective}\left(\operatorname{code}\left(D\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.code_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The computational tag keeps an old vertex unchanged and maps an interior vertex to its edge and natural position. Equality of tags implies equality of actual vertices, including their dependent Fin indices.

**Theorem 1.7 (The computational graph agrees on every actual vertex).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; \forall a \in \operatorname{Vertex}\left(D\right),\; \forall b \in \operatorname{Vertex}\left(D\right),\; \operatorname{Adj}\left(\operatorname{rawGraph}\left(D\right), \operatorname{code}\left(D, a\right), \operatorname{code}\left(D, b\right)\right) \Leftrightarrow \operatorname{Adj}\left(\operatorname{graph}\left(D\right), a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.raw_graph_code_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all actual vertices a,b, adjacency of their tags in rawGraph is equivalent to adjacency in the prescribed graph. Natural tags outside the actual index bounds need not be enumerated. The checker consumes the proved-complete list of actual tags and its proved exact path-edge inventory.

**Theorem 1.8 (Exact vertex cardinality).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(E\right)] \operatorname{FintypeCard}\left(\operatorname{Vertex}\left(D\right)\right) = \operatorname{FintypeCard}\left(V\right) + \sum_{e \in E} (3 \cdot \operatorname{k}\left(D, e\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.card_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite V and E, the vertex cardinality is card(V) plus the sum over e of 3 k(e).

**Theorem 1.9 (Exact edge cardinality).**

$$\forall V \in \mathrm{Type},\; \forall E \in \mathrm{Type},\; \forall D \in \operatorname{Data}\left(V, E\right),\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableEq}\left(E\right)] \operatorname{card}\left(\operatorname{edgeFinset}\left(\operatorname{graph}\left(D\right)\right)\right) = \sum_{e \in E} (3 \cdot \operatorname{k}\left(D, e\right) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.card_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite V and E, the graph has exactly the sum over e of 3 k(e)+1 edges. The edge-inventory bijection supplies this count without enumerating vertex pairs. The module supplies no independence-complex or homology assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.arc_iff_slot`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.card_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.card_vertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.code_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.edge_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.pathVertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.pathVertex_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.raw_graph_code_iff`
