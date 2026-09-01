# Finite Koopman-Localizer Bridge

## Abstract

Finite permutation Koopman pullback has an explicit unit matrix and therefore opens a zero-centered point-gap localizer.

**Definition 1.1 (Finite Koopman matrix).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix` (`✓ std3`).

**Definition 1.2 (Koopman matrix unit).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrixUnit`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrixUnit` (`✓ std3`).

**Theorem 1.3 (Matrix action is Koopman pullback).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_mulVec`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_mulVec` (`✓ std3`). ∎

**Theorem 1.4 (Inverse matrix cancels on the right).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_mul_inverse`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_mul_inverse` (`✓ std3`). ∎

**Theorem 1.5 (Inverse matrix cancels on the left).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_inverse_mul`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_inverse_mul` (`✓ std3`). ∎

**Theorem 1.6 (Zero is a Koopman point gap).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_has_pointGap_zero`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_has_pointGap_zero` (`✓ std3`). ∎

**Theorem 1.7 (Koopman point gap opens the localizer).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanLocalizer_isUnit`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanLocalizer_isUnit` (`✓ std3`). ∎

**Theorem 1.8 (Explicit Koopman localizer inverse).**

Lean statement: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanLocalizer_explicit_inverse`

*Formalization.* `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanLocalizer_explicit_inverse` (`✓ std3`). ∎

## References

- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrixUnit`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_mulVec`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_mul_inverse`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_inverse_mul`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanMatrix_has_pointGap_zero`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanLocalizer_isUnit`
- Truth anchor: `D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.finiteKoopmanLocalizer_explicit_inverse`
- Dependency: [D5/S3/Dynamics/Koopman/FiniteKoopmanUnitary](FiniteKoopmanUnitary.md)
- Dependency: [D5/S3/SpectralTopology/FinitePointGapLocalizer](../../../SpectralTopology/FinitePointGapLocalizer.md)
