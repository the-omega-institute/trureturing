# Finite Hermitian Spectral Localizer

## Abstract

A finite block localizer is Hermitian and its zero-position-scale square splits into the two singular Gram blocks.

**Definition 1.1 (Localized position block).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.positionBlock`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.positionBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered Hermitian position matrix is scaled by the real localization parameter.

**Definition 1.2 (Point-gap block).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.pointGapBlock`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.pointGapBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral operator is shifted by the selected complex reference point.

**Definition 1.3 (Finite Hermitian localizer).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position and point-gap blocks form a doubled Hermitian block matrix.

**Theorem 1.4 (Position block is Hermitian).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.positionBlock_isHermitian`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.positionBlock_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hermiticity of the position matrix is preserved by real centering and scaling.

**Theorem 1.5 (The localizer is Hermitian).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_isHermitian`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate off-diagonal blocks and opposite Hermitian diagonal blocks make the finite localizer Hermitian.

**Theorem 1.6 (Zero position scale leaves the point gap).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero localization scale both spatial diagonal blocks vanish.

**Theorem 1.7 (Zero-scale square gives singular Gram blocks).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale_sq`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring the off-diagonal localizer produces the left and right point-gap Gram matrices on the diagonal.

**Theorem 1.8 (Zero localizer detects a zero point-gap block).**

Lean statement: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale_eq_zero_iff`

*Formalization.* `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero spatial scale the block localizer vanishes exactly when the shifted operator vanishes.

## References

- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.positionBlock`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.pointGapBlock`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.positionBlock_isHermitian`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_isHermitian`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale_sq`
- Truth anchor: `D5/S3/SpectralTopology/FiniteHermitianLocalizer.finiteHermitianLocalizer_zero_scale_eq_zero_iff`
