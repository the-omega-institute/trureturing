# Translation of the Original Orbifold Field

## Abstract

Translation of the Original Orbifold Field

**Definition 1.1 (Diagonal translation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translation is the complex-linear endomorphism assembled from the fixed lattice translation and the actual negative twisted translation.

**Theorem 1.2 (Translation on states).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply each sector translation to its component of the state.

**Theorem 1.3 (Translation annihilates the vacuum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed translation annihilates the lattice vacuum and the twisted component is zero.

**Theorem 1.4 (Fixed-to-fixed covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vv_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vv_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed lattice commutator gives the normalized derivative coefficient.

**Theorem 1.5 (Fixed-to-fixed source translation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vv_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vv_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the fixed Borcherds identity to the zeroth stress mode to translate the source.

**Theorem 1.6 (Fixed action on the negative sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vm_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vm_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Convert the physical derivative of the corrected field to the integer modes of the negative parity slice.

**Theorem 1.7 (Fixed action covariance on the negative sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vm_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vm_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutator of the actual twisted translation with the corrected field restricts to the negative parity slice.

**Theorem 1.8 (Twisted-to-fixed source translation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mm_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mm_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In rank 24 the grade-wise inverse pairing carries the derivative of the normalized coefficient to the original twisted-to-fixed mode.

**Theorem 1.9 (Twisted-to-fixed covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mm_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mm_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In rank 24, specialize the original mixed Jacobi identity to the zeroth stress mode.

**Theorem 1.10 (Right-field covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mv_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mv_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindex the finite original right sum and cancel the terms weighted by the summation index.

**Theorem 1.11 (Right-field source translation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mv_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mv_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Move the twisted translation through the finite original right sum using the fixed-action commutator and derivative.

**Theorem 1.12 (Derivative of the assembled field).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.Y_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.Y_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the positive definite rank-24 lattice, the mode of the translated source is the mode at index n minus one multiplied by minus n.

**Theorem 1.13 (Covariance of the assembled field).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.Y_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.Y_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the positive definite rank-24 lattice, the commutator with diagonal translation has the same derivative coefficient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.T_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.Y_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.Y_translation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mm_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mm_translation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mv_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.mv_translation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vm_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vm_translation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vv_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation.vv_translation`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField](OriginalOrbifoldField.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSourceModeTransport](OriginalSourceModeTransport.md)
