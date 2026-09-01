# Finite Point-Gap Localizer

## Abstract

A finite point-gap unit gives an explicit inverse for the zero-scale Hermitian localizer.

**Definition 1.1 (Finite point gap).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.HasFinitePointGap`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.HasFinitePointGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shifted finite operator is required to be a unit in its matrix ring.

**Definition 1.2 (Off-diagonal point-gap localizer).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A matrix block and its conjugate transpose form a Hermitian doubled localizer.

**Definition 1.3 (Explicit localizer inverse).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizerInverse`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizerInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two off-diagonal blocks are formed from the inverse point-gap unit and its conjugate transpose.

**Theorem 1.4 (Explicit right inverse).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer_mul_inverse`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer_mul_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The off-diagonal localizer multiplied by its proposed inverse is the identity.

**Theorem 1.5 (Explicit left inverse).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer_inverse_mul`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer_inverse_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proposed inverse multiplied by the off-diagonal localizer is the identity.

**Theorem 1.6 (Point gap opens the localizer gap).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.zero_scale_localizer_isUnit_of_pointGap`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.zero_scale_localizer_isUnit_of_pointGap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite matrix point gap makes the zero-position-scale Hermitian localizer invertible.

**Theorem 1.7 (Zero-scale inverse formula).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.zero_scale_localizer_explicit_inverse`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.zero_scale_localizer_explicit_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse localizer is exactly the off-diagonal matrix built from the inverse shifted operator.

**Theorem 1.8 (Identity has a zero-centered point gap).**

Lean statement: `D5/S3/SpectralTopology/FinitePointGapLocalizer.identity_hasFinitePointGap_zero`

*Formalization.* `D5/S3/SpectralTopology/FinitePointGapLocalizer.identity_hasFinitePointGap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity finite operator provides an inhabited point-gap witness.

## References

- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.HasFinitePointGap`
- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer`
- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizerInverse`
- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer_mul_inverse`
- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.offDiagonalLocalizer_inverse_mul`
- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.zero_scale_localizer_isUnit_of_pointGap`
- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.zero_scale_localizer_explicit_inverse`
- Truth anchor: `D5/S3/SpectralTopology/FinitePointGapLocalizer.identity_hasFinitePointGap_zero`
- Dependency: [D5/S3/SpectralTopology/FiniteHermitianLocalizer](FiniteHermitianLocalizer.md)
