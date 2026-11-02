# LatticeRealNullFrame

## Abstract

Original real Lorentzian lattice geometry

Classical real quadratic-form geometry on the original integral-lattice coordinates, using pinned Mathlib Sylvester signature and positive-form results. This local geometry proves no BPZ polynomial positivity, full no-ghost or BRST theorem, or string/Monster/AdS completion.

**Theorem 1.1 (Signature normal form).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_lorentzNormalForm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_lorentzNormalForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two original real Gram signature equalities force exactly one negative Sylvester weight and every other weight to +1. The isometry is derived, rather than supplied.

**Theorem 1.2 (Charge-adapted Lorentz plane).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_charge_plane`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_charge_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rank at least two and every nonzero original integral charge, the signature hypotheses construct a real time-space plane containing that charge. Its spatial orientation is chosen so that -a+c is nonzero, including a purely temporal charge and either null orientation.

**Definition 1.3 (Original real splitting).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.splitting`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.splitting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit map v ↦ (-g(time,v),g(space,v),projection(v)) has a proved inverse in the original real Gram coordinates.

**Theorem 1.4 (Real transverse dimension).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.finrank_K_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.finrank_K_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The simultaneous original Gram kernels have real dimension rank minus two, derived from the explicit real linear equivalence.

**Theorem 1.5 (Positive real restriction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.positive_K_R`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.positive_K_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual restriction of Q_R to the actual two Gram kernels is positive definite; it is not a supplied complement or a statement about complex bilinear positivity.

**Theorem 1.6 (Faithful complex projection).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complex_projection_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complex_projection_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing complex NullFrame projection of the literal coordinatewise complexification equals complexification of the proved real projection, in the original coordinates.

**Theorem 1.7 (Real orthonormal basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_real_orthonormalBasis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_real_orthonormalBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sylvester diagonalization of the actual positive restricted quadratic form forces every basis weight to +1, including the empty basis in rank two.

**Definition 1.8 (Complex coordinates on the actual complement).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexCoordinates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual Gram coefficient map has inverse given by the explicit complex span of the real orthonormal basis. Real and imaginary coordinate expansions prove the inverse law.

**Theorem 1.9 (Complex orthonormal Gram matrix).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexBasis_gram`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexBasis_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed complex basis of the actual NullFrame.K has the identity complex bilinear Gram matrix.

**Theorem 1.10 (Real Hermitian diagonal).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.hermitian_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.hermitian_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinatewise conjugation gives g(conj(z),z)=Q_R(re(z))+Q_R(im(z)), with the right side embedded from the real numbers. This is separate from positivity of the complex bilinear form.

**Theorem 1.11 (Conjugation-fixed basis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexBasis_conjugation_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexBasis_conjugation_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each complex basis vector is the literal coordinatewise complexification of a real basis vector and is fixed by the actual original-coordinate conjugation.

**Theorem 1.12 (Positive Hermitian transverse diagonal).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.hermitian_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.hermitian_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero vector of the actual complex transverse space has strictly positive real Hermitian diagonal, because its real and imaginary parts lie in the positive real complement.

**Theorem 1.13 (Signature to original real geometry).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_original_real_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_original_real_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume exactly original D, rank at least two, sigNeg(Q_R D)=1, sigPos(Q_R D)=rank-1, and nonzero original p:Charge D. Construct the real null pair with mutual pairing one; nonzero real and complex charge detection; both transverse charge projections zero; both dimensions rank-2; positive real restriction; a conjugation-fixed orthonormal complex basis; and positive Hermitian transverse diagonal. No determinant, inverse-Gram, frame, splitting or positive-complement premise is added.

Transient anonymous applications use the retained generic coordinateEquiv/allChargeEquiv transport and frequency grading, and the original zero-mode pairing. They do not introduce named wrappers or change integral charge labels. Rank-two and rank-26 inhabited checks are transient acceptance evidence, not independent retained mathematical content. The Reg mirror preserves exact source-family bridges; native compilation alone does not validate any four-slot registration.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexBasis_conjugation_fixed`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexBasis_gram`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complexCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.complex_projection_bridge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_charge_plane`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_lorentzNormalForm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_original_real_geometry`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.exists_real_orthonormalBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.finrank_K_R`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.hermitian_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.hermitian_positive`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.positive_K_R`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame.splitting`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence](LatticeNullFrameExistence.md)
