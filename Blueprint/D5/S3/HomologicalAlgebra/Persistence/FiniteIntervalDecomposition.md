# Homogeneous Interval Bases for Finite Diagrams

## Abstract

Every actual finite diagram over a field has a finite homogeneous interval basis.

**Definition 1.1 (One occurrence set across all vertices).**

Lean statement: `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.IntervalBasis`

*Formalization.* `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.IntervalBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

An interval basis contains a finite occurrence type, birth and last indices b(a) <= j(a), and a vector w(a,i) at every vertex. The vectors vanish outside their supports. At vertex i the vectors indexed by occurrences with b(a) <= i <= j(a) form an actual basis. For i <= k, the actual map sends w(a,i) to w(a,k) when b(a) <= i and k <= j(a), and to zero otherwise.

**Theorem 1.2 (Constructing the simultaneous bases from arbitrary arrows).**

$$\forall K \in Type, n \in \operatorname{Nat}\left(\right), V \in \operatorname{VertexSpaces}\left(n\right), F \in \operatorname{Diagram}\left(K, V\right),\; \left(\operatorname{Field}\left(K\right) \land \operatorname{FiniteDimensionalVertices}\left(K, V\right)\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{IntervalBasis}\left(F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.exists_interval_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ulrich Bauer and Michael Lesnick; William Crawley-Boevey; Frédéric Chazal, Vin de Silva, Marc Glisse and Steve Oudot (2015). *Interval decomposition and induced matching for persistence modules*. URL: <https://arxiv.org/abs/1311.3681v4>.

*Commentary.*

K is any field and the vertices are Fin(n). Each V(i) is finite-dimensional without a uniform supplied dimension bound. The diagram contains arbitrary actual forward maps with identity and composition laws. The conclusion constructs an interval basis, rather than assuming one as a classifier input.

Strong induction uses the sum of the vertex finranks. If every vertex is zero, the occurrence type is empty. Otherwise a natural interval retraction gives an actual kernel diagram of strictly smaller total dimension. Its recursively constructed bases are combined with the supported singleton line bases using the vertexwise product splitting. The occurrence type is enlarged by one globally, not independently at each vertex. Naturality holds for every resulting occurrence.

The supported basis coordinate isomorphisms give the finite-diagram interval classification. Empty chains and all-zero diagrams are included. The last vertex is an ordinary vertex and may be supported; no terminal zero is imposed. Real extension, multiset uniqueness on common refinements and exact stability are distinct further results.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.IntervalBasis`
- Truth anchor: `D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.exists_interval_basis`
- Dependency: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit](FiniteIntervalSplit.md)
