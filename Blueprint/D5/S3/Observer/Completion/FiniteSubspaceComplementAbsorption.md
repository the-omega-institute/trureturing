# Finite Subspace Complement Absorption

## Abstract

Removing a finite-dimensional subspace preserves the Hilbert dimension and unitary type of an infinite-dimensional Hilbert space.

**Theorem 1.1 (A finite extraction leaves a full-dimensional complement).**

$$\forall K \in Type, H \in Type, M \in \operatorname{Submodule}\left(K, H\right),\; \left(\operatorname{RCLike}\left(K\right) \land \left(\operatorname{NormedAddCommGroup}\left(H\right) \land \left(\operatorname{InnerProductSpace}\left(K, H\right) \land \left(\operatorname{CompleteSpace}\left(H\right) \land \left(\operatorname{FiniteDimensional}\left(K, M\right) \land \left(\neg \operatorname{FiniteDimensional}\left(K, H\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists I \in Type,\; \exists bperp \in \operatorname{HilbertBasis}\left(I, K, \operatorname{orthogonalComplement}\left(M\right)\right),\; \exists b \in \operatorname{HilbertBasis}\left(I, K, H\right),\; \exists U \in \operatorname{LinearIsometryEquiv}\left(K, \operatorname{orthogonalComplement}\left(M\right), H\right),\; \exists Q \in \operatorname{LinearIsometryEquiv}\left(K, \operatorname{SubmoduleQuotient}\left(H, M\right), H\right),\; U = \operatorname{trans}\left(\operatorname{repr}\left(bperp\right), \operatorname{symm}\left(\operatorname{repr}\left(b\right)\right)\right) \land Q = \operatorname{trans}\left(\operatorname{quotientEquivOrthogonal}\left(M\right), U\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/FiniteSubspaceComplementAbsorption.finite_subspace_complement_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common index type carries an explicit Hilbert basis of the orthogonal complement and an explicit Hilbert basis of the ambient space, which states equality of Hilbert dimension.

The complement unitary is the composition of the two basis representations. The quotient unitary then composes the canonical quotient-to-orthogonal-complement isometry with that unitary.

The proof extends a finite orthonormal basis of the extracted subspace to an ambient Hilbert basis. It applies the frozen basis-tail construction to the remaining coordinates and uses finite-cardinal absorption only to reindex that tail.

## References

- Truth anchor: `D5/S3/Observer/Completion/FiniteSubspaceComplementAbsorption.finite_subspace_complement_absorption`
- Dependency: [D5/S3/Quantum/Algebra/QuotientOrthogonalComplement](../../Quantum/Algebra/QuotientOrthogonalComplement.md)
- Dependency: [D5/S3/Quantum/Completion/TransfiniteBasisResidualTower](../../Quantum/Completion/TransfiniteBasisResidualTower.md)
