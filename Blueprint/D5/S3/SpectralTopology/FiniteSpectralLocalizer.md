# Finite Spectral Localizer

## Abstract

A finite non-Hermitian point gap admits a Hermitian chiral localizer.

**Definition 1.1 (Shifted position observable).**

Lean statement: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.positionShift`

*Formalization.* `D5/S3/SpectralTopology/FiniteSpectralLocalizer.positionShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite position matrix is shifted by a real reference coordinate.

**Definition 1.2 (Shifted spectral operator).**

Lean statement: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.spectralShift`

*Formalization.* `D5/S3/SpectralTopology/FiniteSpectralLocalizer.spectralShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite operator is shifted by a complex reference point.

**Definition 1.3 (Finite spectral localizer).**

Lean statement: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.finiteSpectralLocalizer`

*Formalization.* `D5/S3/SpectralTopology/FiniteSpectralLocalizer.finiteSpectralLocalizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shifted position and spectral operators form one doubled Hermitian block matrix.

**Definition 1.4 (Chiral grading).**

Lean statement: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.chiralGrading`

*Formalization.* `D5/S3/SpectralTopology/FiniteSpectralLocalizer.chiralGrading` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The doubled carrier is graded by positive and negative identity blocks.

**Definition 1.5 (Finite point gap).**

Lean statement: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.HasPointGap`

*Formalization.* `D5/S3/SpectralTopology/FiniteSpectralLocalizer.HasPointGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point gap means that the shifted finite operator is a matrix unit.

**Definition 1.6 (Signed Hermitian inertia).**

Lean statement: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.hermitianSignature`

*Formalization.* `D5/S3/SpectralTopology/FiniteSpectralLocalizer.hermitianSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature reuses the repository positive and negative Hermitian indices.

**Theorem 1.7 (Point gap equals zero-scale localizer invertibility).**

$$\operatorname{HasPointGap}(H, z) \iff \operatorname{IsUnit}(\operatorname{finiteSpectralLocalizer}(X, H, 0, x, z))$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/FiniteSpectralLocalizer.has_point_gap_iff_zero_scale_localizer_isUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real position shifts preserve Hermitianity, so a Hermitian position observable makes the complete block localizer Hermitian; at zero position scale only the spectral shift and its conjugate transpose remain, independently of the position input, and the square is the orthogonal block sum of the two spectral-shift Gram matrices.

The chiral grading is involutive, anticommutes with the zero-scale localizer, negates it under conjugation, and pairs every nonzero eigenvector at an eigenvalue with one at its negative; Hermitian negation exchanges the strictly positive and strictly negative inertia counts, forcing the zero-scale inertia balance and the vanishing of the finite localizer signature.

Over the complex numbers a finite point gap is exactly a nonzero shifted determinant, and it is equivalent to invertibility of the zero-scale chiral Hermitianization, of its determinant, of its square, and of both spectral-shift Gram blocks; conjugate transpose preserves the point-gap condition when the reference point is conjugated.

## References

- Truth anchor: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.HasPointGap`
- Truth anchor: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.chiralGrading`
- Truth anchor: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.finiteSpectralLocalizer`
- Truth anchor: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.has_point_gap_iff_zero_scale_localizer_isUnit`
- Truth anchor: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.hermitianSignature`
- Truth anchor: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.positionShift`
- Truth anchor: `D5/S3/SpectralTopology/FiniteSpectralLocalizer.spectralShift`
