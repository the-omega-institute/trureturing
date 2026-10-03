# Homogeneous Interval Bases for Finite Diagrams

## Abstract

Every actual finite diagram over a field has a finite homogeneous interval basis.

**Theorem 1.1 (Constructing the simultaneous bases from arbitrary arrows).**

$$\forall K \in Type, n \in \operatorname{Nat}\left(\right), V \in \operatorname{VertexSpaces}\left(n\right), F \in \operatorname{ModuleCatFunctor}\left(K, V\right),\; \left(\operatorname{Field}\left(K\right) \land \operatorname{FiniteDimensionalVertices}\left(K, V\right)\right) \Rightarrow \operatorname{ExistsFiniteOccurrenceEndpointsVectorsBasesWithNaturality}\left(F\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.exists_interval_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

K is any field and the vertices are Fin(n). Each V(i) is finite-dimensional without a uniform supplied dimension bound. The existing Fin(n)-indexed ModuleCat functor contains arbitrary actual forward maps with identity and composition laws. The conclusion constructs finite endpoint, vector and basis witnesses, rather than assuming one as a classifier input.

Strong induction uses the sum of the vertex finranks. If every vertex is zero, the occurrence type is empty. Otherwise a natural interval retraction gives an actual kernel diagram of strictly smaller total dimension. Its recursively constructed bases are combined with the supported singleton line bases using the vertexwise product splitting. The occurrence type is enlarged by one globally, not independently at each vertex. Naturality holds for every resulting occurrence.

The supported basis coordinate isomorphisms give the finite-diagram interval classification. Empty chains and all-zero diagrams are included. The last vertex is an ordinary vertex and may be supported; no terminal zero is imposed. Real extension, multiset uniqueness on common refinements and exact stability are distinct further results.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.exists_interval_basis`
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit](FiniteIntervalSplit.md)
