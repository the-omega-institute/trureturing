# Offline-Zero Golden-Period Monodromy

## Abstract

Golden-period sampling turns an offline-zero character into reciprocal real monodromy branches, hyperbolic exactly off the unitary boundary.

**Definition 1.1 (The golden-period monodromy realizes the offline-zero geometry).**

Lean statement: `D5/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy.offline_zero_geometric_definition`

*Formalization.* `D5/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy.offline_zero_geometric_definition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized Mellin mode is reused from OfflineZeroCharacter. Sampling its two reciprocal radial branches at twice the logarithm of the golden ratio gives a real diagonal two-by-two monodromy with determinant one.

Its trace discriminant is four times the square of the hyperbolic sine of the radial displacement. Consequently the monodromy is hyperbolic exactly when the character lies off the unitary boundary.

The definition is realized nonvacuously by the existing nonunitary offline-zero witness. The source's closing Solenoid language is not promoted to an unsupported uniqueness or maximality claim.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy.offline_zero_geometric_definition`
- Dependency: [D5/S3/Weil/ZetaLinear/OfflineZeroCharacter](OfflineZeroCharacter.md)
