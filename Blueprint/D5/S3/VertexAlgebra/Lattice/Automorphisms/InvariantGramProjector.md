# Invariant Gram Projectors

## Abstract

Orthogonal projection onto an invariant real subspace commutes with each isometry and gives compatible real and complex matrix identities.

Let B be a symmetric positive-definite bilinear form on a finite-dimensional real vector space V. Let W be a proper nonzero subspace. Each member g of the indexed family of linear equivalences preserves B and satisfies g(x) ∈ W if and only if x ∈ W.

**Theorem 1.1 (Equivariant orthogonal projection).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a linear endomorphism P with range W and P² = P, distinct from zero and the identity. It satisfies B(Px,y) = B(x,Py) for all x,y and commutes with each g. Positivity makes the restricted form on W nondegenerate, giving the decomposition into W and its orthogonal complement. The isometries preserve both summands, so projection commutes with them.

**Theorem 1.2 (Real matrix identities).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real basis with a finite index type and decidable equality, let G be the matrix of B and M(g) the matrix of the isometry g in that basis. There is a real matrix P with P² = P, P ≠ 0 and P ≠ 1. It satisfies PᵀG = GP and commutes with each M(g). The transpose equation is the matrix form of bilinear self-adjointness.

**Theorem 1.3 (Complex matrix identities).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector_complex_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector_complex_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed the entries of G and M(g) into ℂ. There is a complex matrix P with P² = P, P ≠ 0 and P ≠ 1, satisfying PᵀG = GP and commuting with every complexified M(g). The injective ring map preserves the real matrix equations and both inequalities. Self-adjointness here uses the bilinear transpose.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector_complex_matrix`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector.exists_invariant_projector_matrix`
