# Fejer smoothing and Gaussian Hermite identities

## Abstract

Fourier inversion of the tent function and Gaussian Hermite integrals give signed density comparison bounds.

**Theorem 1.1 (The Fejer kernel has unit mass).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.integral_fejerKernel`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.integral_fejerKernel` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

For every positive bandwidth, the squared-sinc Fejer kernel is integrable and its integral is one. The tent function and its Fourier transform supply a probability smoothing kernel with compact Fourier support.

**Theorem 1.2 (A translated and rescaled Fourier pair).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.fourier_gTent`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.fourier_gTent` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

A modulated squared-sinc function transforms into a translated and rescaled tent. Positive bandwidth fixes the support interval and the scaling factor.

**Theorem 1.3 (A Fourier bound for a signed comparison density).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.abs_measure_Iic_sub_densityCDF_le_charFun`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.abs_measure_Iic_sub_densityCDF_le_charFun` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Compare the distribution function of a probability measure with the integral of an integrable real function. The comparison function may have either sign. A bound on its absolute integral over intervals controls the ramp approximation error; a weighted characteristic-function difference controls the smoothed error.

**Theorem 1.4 (Integrating the first Hermite correction).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.densityCDF_edgeworthDensity`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.densityCDF_edgeworthDensity` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

The first Edgeworth density is the standard Gaussian density multiplied by one plus a cubic Hermite correction. Its integral over a lower half-line is the Gaussian distribution function plus the quadratic Hermite correction.

**Theorem 1.5 (The characteristic function of the signed Edgeworth density).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.charFunDensity_edgeworthDensity`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.charFunDensity_edgeworthDensity` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Gaussian integration by parts evaluates the cubic Hermite Fourier integral. The result is the Gaussian characteristic function multiplied by its first cubic correction, with the same coefficient as in the density.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.abs_measure_Iic_sub_densityCDF_le_charFun`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.charFunDensity_edgeworthDensity`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.densityCDF_edgeworthDensity`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.fourier_gTent`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.integral_fejerKernel`
