# Cartesian products of finite complete graphs

## Abstract

Changing one coordinate gives a regular Cartesian product of complete graphs.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Definition 1.1 (One-coordinate adjacency).**

$$\forall q \in \mathit{Nat},\; \forall A \in \mathit{Type},\; \forall x \in \mathrm{Fin}\left(q\right) \to A,\; \forall y \in \mathrm{Fin}\left(q\right) \to A,\; \operatorname{SimpleGraph}.\operatorname{Adj}\left(\mathrm{coordinateGraph}\left(q, A\right), x, y\right) \Leftrightarrow (\exists a \in \mathrm{Fin}\left(q\right),\; (\mathrm{val}\left(x, a\right) \ne \mathrm{val}\left(y, a\right)) \land (\forall b \in \mathrm{Fin}\left(q\right),\; (b \ne a) \Rightarrow (\mathrm{val}\left(x, b\right) = \mathrm{val}\left(y, b\right))))$$

*Formalization.* `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.coordinateGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjacency relation says that x and y disagree at one coordinate a and agree at every other coordinate. This is exactly the Cartesian product of q copies of the complete graph on the alphabet type. The definition includes the empty-coordinate case.

**Theorem 1.2 (Degree and undirected edge count).**

$$\forall q \in \mathit{Nat},\; \forall A \in \mathit{Type},\; [\mathrm{Fintype}\left(A\right)](\operatorname{SimpleGraph}.\operatorname{IsRegularOfDegree}\left(\mathrm{coordinateGraph}\left(q, A\right), q \cdot (\operatorname{Fintype}.\operatorname{card}\left(A\right) - 1)\right)) \land (2 \cdot \operatorname{Finset}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(\mathrm{coordinateGraph}\left(q, A\right)\right)\right) = \operatorname{Fintype}.\operatorname{card}\left(A\right)^{q} \cdot (q \cdot (\operatorname{Fintype}.\operatorname{card}\left(A\right) - 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.regular_and_edge_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each neighbour is uniquely specified by the coordinate to replace and by its replacement value, which differs from the old value. The degree-sum identity then counts undirected edges. The conclusion also holds for an empty alphabet and for zero coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.coordinateGraph`
- Truth anchor: `D5/S3/Quantum/Fermionic/CompleteCartesianGraph.regular_and_edge_count`
