# Full-matrix Weyl star correction

## Abstract

The complete normalized Weyl family supplies a contractive diagonal for every positive matrix size and hence the same exact-correction constants.

Fix a natural n with n nonzero. Weyl coordinates are ZMod n, with all n^2 ordered labels. The final source coordinates are Fin n, obtained by the canonical finite reindexing. The source is the full matrix algebra on those coordinates; its norm is the Euclidean L2 operator norm and its star is conjugate transpose. This includes n=1 and every composite size. The target is any complex C-star algebra, independently of n.

The actual word U(a,b) is shiftMatrix(n)^a.val times clockMatrix(n)^b.val. The left leg is (n^2)^(-1) star(U(a,b)); the right leg is U(a,b). In particular the adjoint retains the Weyl phase. Each word is unitary, both word and adjoint have operator norm one, and the weighted sum of norm products is exactly one.

Character orthogonality evaluates the weighted tensor coefficient at (i,j,k,l) to n^(-1) when l=i and k=j, and to zero otherwise. Thus the tensor is n^(-1) sum E(i,j) tensor E(j,i). Matrix-unit multiplication proves centrality for every full source matrix. A complex star-algebra equivalence transports the packet to Fin n and preserves the operator norm. The product of the legs sums to the identity. The diagonal defined here supplies all three properties to the correction theorem.

**Theorem 1.1 (Uniform correction in the actual full matrix algebra).**

$$\forall n \in \operatorname{Nat}\left(\right),\; [\operatorname{NeZero}\left(n\right)] \forall A \in \operatorname{Type}\left(\right),\; [\operatorname{CStarAlgebra}\left(A\right)] \forall f \in \operatorname{ComplexCLM}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right)\right), A\right),\; \forall d \in \operatorname{Real}\left(\right),\; \left(0 \le d \land \left(d \le \frac{1}{32} \land \left(\operatorname{PreservesStar}\left(f\right) \land \left(\operatorname{DefectBound}\left(f, d\right) \land \left\lVert f\left(1\right) - 1 \right\rVert \le \frac{1}{4}\right)\right)\right)\right) \Rightarrow \left(\exists rho \in \operatorname{ComplexStarAlgHom}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right)\right), A\right),\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right)\right),\; \left\lVert rho\left(X\right) - f\left(X\right) \right\rVert \le \frac{8 \cdot d}{3} \cdot \left\lVert X \right\rVert\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/WeylStarCorrector.exists_matrix_star_hom_close` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the finite-diagonal correction to this exact Weyl packet. PreservesStar is exact star preservation, while DefectBound f d quantifies norm(f(XY)-f(X)f(Y))<=d norm(X) norm(Y) over every pair of source matrices. The initial unit error is at most one quarter, and 0<=d<=1/32. The output is a genuine unital complex star-algebra homomorphism with the stated distance from this same f.

The tensor, unitary and normalization identities supply a dimension-free norm budget. No unweighted n^2 error sum is introduced. The construction requires no CP or UCP data, no column compatibility, no supplied representation and no equality between source and target dimensions. For a Hilbert-operator target the complex inner-product structure and completeness must belong to the actual target space. No algebra structure on an unrelated nonassociative product is asserted.

The finite averaging formula is associated with arXiv:2405.02434v2. The conclusion is the matrix application of the finite-diagonal theorem; deriving a particular compressed action and its quantitative input estimates is a separate mathematical obligation.

## References

- Truth anchor: `D5/S3/Quantum/Approximate/WeylStarCorrector.exists_matrix_star_hom_close`
- Dependency: [D5/S3/Observer/MatrixUnitCertificate](../../Observer/MatrixUnitCertificate.md)
- Dependency: [D5/S3/Quantum/Approximate/FiniteStarNewton](FiniteStarNewton.md)
- Dependency: [D5/S3/Quantum/Magic/SubspaceStabilizerEntropy](../Magic/SubspaceStabilizerEntropy.md)
