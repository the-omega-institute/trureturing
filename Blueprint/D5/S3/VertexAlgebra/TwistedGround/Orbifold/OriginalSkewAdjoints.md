# Adjoints of the Original Corrected Field and Translation

## Abstract

Adjoints of the Original Corrected Field and Translation

**Theorem 1.1 (Corrected-field transpose on a whole lattice grade).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.actual_corrected_adjoint_of_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.actual_corrected_adjoint_of_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive definite lattice with unit Gram determinant, the transpose of coefficient e on a homogeneous source of integer grade d is the sum of original corrected-field coefficients at indices −e − 4d + 2j on states obtained by applying Sugawara mode one j times. The terms are weighted by (−1) to the power d and inverse factorials. Nonnegative charge energy bounds each monomial's oscillator weight by the grade, so Sugawara nilpotence gives a common cutoff at the natural part of d. The source can have either theta parity.

**Theorem 1.2 (Transpose on the fixed grade).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.actual_corrected_grade_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.actual_corrected_grade_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the whole-grade transpose to the underlying homogeneous state of the fixed grade.

**Theorem 1.3 (Transpose of original translation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.sourcePairing_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.sourcePairing_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the original source pairing, translation transposes to the inverse-Gram Sugawara mode one. The all-state BPZ formula applied to the grade-two stress state has a single surviving term because mode one kills that state.

**Theorem 1.4 (Transpose of fixed translation powers).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.sourcePairing_fixedTranslation_pow`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.sourcePairing_fixedTranslation_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterate the source-pairing identity to move every power of fixed translation to the corresponding Sugawara power on the full source carrier.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.actual_corrected_adjoint_of_grade`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.actual_corrected_grade_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.sourcePairing_fixedTranslation_pow`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints.sourcePairing_translation`
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/AllStateTranspose](../../SourceBPZ/AllStateTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedTranslation](../MixedTranslation.md)
