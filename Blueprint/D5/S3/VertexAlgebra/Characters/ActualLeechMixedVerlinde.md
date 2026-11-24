# Actual Leech Mixed Verlinde Comparison

## Abstract

The finite character calculation and the native Leech mixed field spaces have matching multiplicities.

**Definition 1.1 (Finite Verlinde coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.verlindeCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.verlindeCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is the normalized triple product sum using the matrix acting on the four literal sector characters.

**Definition 1.2 (Twisted sector label).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.twistedLabel`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.twistedLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Negative oscillator parity selects B and positive oscillator parity selects C.

**Definition 1.3 (Native mixed coefficient line).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixedCoefficientSpace`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixedCoefficientSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The line is the span of the native mixed field's coefficients in the space of coefficient families.

**Theorem 1.4 (Lawful coefficient families).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mem_mixedCoefficientSpace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mem_mixedCoefficientSpace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual multiplicity-one theorem identifies the line with all coefficient families satisfying the lower truncation, translation and signed Jacobi laws of a lawful mixed field.

**Theorem 1.5 (Native field dimension).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixedCoefficientSpace_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixedCoefficientSpace_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native field has a nonzero coefficient in each direction, so each coefficient space has complex dimension one.

**Theorem 1.6 (Mixed multiplicity comparison).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixed_verlinde_agrees_with_native_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixed_verlinde_agrees_with_native_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by the anti-fixed lattice label selects C from B and B from C in the finite coefficient sum. The selected entry equals the dimension of the corresponding lawful field space, and the other entries in each row vanish.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mem_mixedCoefficientSpace`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixedCoefficientSpace`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixedCoefficientSpace_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.mixed_verlinde_agrees_with_native_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.twistedLabel`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechMixedVerlinde.verlindeCoefficient`
- Dependency: [D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters](ActualLeechSectorCharacters.md)
