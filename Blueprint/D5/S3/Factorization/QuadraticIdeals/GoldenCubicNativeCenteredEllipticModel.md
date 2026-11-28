# The centered cubic chart for the native elliptic curve

## Abstract

The centered native cubic is Eisenstein and gives exact elliptic model coefficients.

**Theorem 1.1 (The cubic centered at the actual Lucas coordinate is Eisenstein at three).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel.native_centered_eisenstein`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel.native_centered_eisenstein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The centered cubic is z cubed plus three L z squared minus nine z minus three L. The native Lucas coordinate is a unit modulo three.

**Theorem 1.2 (The actual centered root gives exact model coefficient identities).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel.local_model_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel.local_model_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by L plus the root and scaling by its square produces the displayed four transformed coefficient and discriminant identities. No valuation-extension or arithmetic inertia theorem is asserted by this endpoint.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel.local_model_coefficients`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel.native_centered_eisenstein`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeElliptic](GoldenCubicNativeElliptic.md)
