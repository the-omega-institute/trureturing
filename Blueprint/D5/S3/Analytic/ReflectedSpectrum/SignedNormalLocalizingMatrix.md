# Signed-Normal Localizing Matrix

## Abstract

A positive-mass signed-normal atom has a positive ordinary Hankel matrix and a negative shifted localizing witness exactly off the reflection boundary.

**Definition 1.1 (Signed-normal support coordinate).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalLocation`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalLocation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support coordinate reuses the frozen reflected-pair signed determinant. It is the negative square of the reflected split.

**Definition 1.2 (Single-atom signed-normal moments).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalAtomMoment`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalAtomMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real mass and signed support coordinate determine the scalar moment sequence used by the ordinary and shifted Hankel matrices.

**Definition 1.3 (Ordinary positive-mass Hankel matrix).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalHankelMatrix`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalHankelMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary Hankel truncation is stored as a nonnegative scalar multiple of a rank-one outer product.

**Definition 1.4 (Shifted support-localizing matrix).**

Lean statement: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalLocalizingMatrix`

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalLocalizingMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first shifted matrix multiplies the same rank-one Gram factor by the signed support coordinate. This separates support location from mass positivity.

**Theorem 1.5 (Positive Hankel with negative localizing witness).**

$$\operatorname{PosSemidef}(\operatorname{hankel}(m, \delta)) \land \operatorname{hermForm}(\operatorname{localizing}(m, \delta), \operatorname{e}()) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signed_normal_atom_hankel_localizing_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed-normal support coordinate is the negated square of the reflection offset, so it is strictly negative exactly off the reflection boundary; nonnegative mass makes every ordinary Hankel truncation positive semidefinite.

The unit-coordinate readout of the shifted localizing matrix is the mass times the support coordinate, so a positive-mass off-boundary atom simultaneously carries positive ordinary Hankel truncations and a finite negative support-localizing certificate — the two-sided witness separating boundary from off-boundary support.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalAtomMoment`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalHankelMatrix`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalLocalizingMatrix`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signedNormalLocation`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.signed_normal_atom_hankel_localizing_certificate`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare](../Adelic/ReflectedGrowthPairNegativeSquare.md)
