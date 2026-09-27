# Gaussian Hermite and Edgeworth identities

## Abstract

Gaussian Hermite integration evaluates the signed first Edgeworth density and its characteristic function.

**Theorem 1.1 (Integrating the first Hermite correction).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.densityCDF_edgeworthDensity`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.densityCDF_edgeworthDensity` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

The first Edgeworth density is the standard Gaussian density multiplied by one plus a cubic Hermite correction. Its integral over a lower half-line is the Gaussian distribution function plus the quadratic Hermite correction.

**Theorem 1.2 (The characteristic function of the signed Edgeworth density).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.charFunDensity_edgeworthDensity`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.charFunDensity_edgeworthDensity` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Gaussian integration by parts evaluates the cubic Hermite Fourier integral. The result is the Gaussian characteristic function multiplied by its first cubic correction, with the same coefficient as in the density.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.charFunDensity_edgeworthDensity`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.densityCDF_edgeworthDensity`
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanSignedSmoothing](StatLeanSignedSmoothing.md)
