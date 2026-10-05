# Cartesian products of finite complete graphs

## Abstract

Changing one coordinate gives a regular Cartesian product of complete graphs.

Nat is the natural-number type and Type is an arbitrary type. Fin(q) has q labels, Fun(A,B) is the function type A → B, and card denotes finite-type cardinality. SimpleGraphMk(R) denotes the simple graph with the displayed symmetric irreflexive adjacency relation R; its symmetry and irreflexivity proof fields are suppressed. edgeCount(G) is the cardinality of G.edgeFinset, counting each undirected edge once. tsub denotes natural subtraction truncated at zero. IsRegularOfDegree(G,D) means that every vertex of G has degree D. Fintype is the usual finite-type enumeration instance.

**Definition 1.1 (One-coordinate adjacency).**

$$\forall q \in \mathit{Nat},\; \forall A \in \mathit{Type},\; (\mathrm{coordinateGraph}\left(q, A\right):\mathrm{SimpleGraph}\left(\mathrm{Fun}\left(\mathrm{Fin}\left(q\right), A\right)\right)) = \mathrm{SimpleGraphMk}\left(x:\mathrm{Fun}\left(\mathrm{Fin}\left(q\right), A\right) \mapsto y:\mathrm{Fun}\left(\mathrm{Fin}\left(q\right), A\right) \mapsto \exists a \in \mathrm{Fin}\left(q\right),\; (\mathrm{val}\left(x, a\right) \ne \mathrm{val}\left(y, a\right)) \land (\forall b \in \mathrm{Fin}\left(q\right),\; (b \ne a) \Rightarrow (\mathrm{val}\left(x, b\right) = \mathrm{val}\left(y, b\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.coordinateGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjacency relation says that x and y disagree at one coordinate a and agree at every other coordinate. This is exactly the Cartesian product of q copies of the complete graph on the alphabet type. The definition includes the empty-coordinate case.

**Theorem 1.2 (Degree and undirected edge count).**

$$\forall q \in \mathit{Nat},\; \forall A \in \mathit{Type},\; [\mathrm{Fintype}\left(A\right)](\mathrm{IsRegularOfDegree}\left(\mathrm{coordinateGraph}\left(q, A\right), q \cdot (\mathrm{tsub}\left(\mathrm{card}\left(A\right), 1\right))\right)) \land (2 \cdot \mathrm{edgeCount}\left(\mathrm{coordinateGraph}\left(q, A\right)\right) = \mathrm{card}\left(A\right)^{q} \cdot (q \cdot (\mathrm{tsub}\left(\mathrm{card}\left(A\right), 1\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.regular_and_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each neighbour is uniquely specified by the coordinate to replace and by its replacement value, which differs from the old value. The degree-sum identity then counts undirected edges. The conclusion also holds for an empty alphabet and for zero coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.coordinateGraph`
- Truth anchor: `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.regular_and_edge_count`
