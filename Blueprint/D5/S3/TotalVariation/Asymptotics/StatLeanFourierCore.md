# Fejer smoothing and the tent Fourier pair

## Abstract

The tent and squared-sinc Fourier pair provides Fejer smoothing and Fourier representations of ramp differences.

**Theorem 1.1 (The Fejer kernel has unit mass).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore.integral_fejerKernel`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore.integral_fejerKernel` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

For every positive bandwidth, the squared-sinc Fejer kernel is integrable and its integral is one. The tent function and its Fourier transform supply a probability smoothing kernel with compact Fourier support.

**Theorem 1.2 (A translated and rescaled Fourier pair).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore.fourier_gTent`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore.fourier_gTent` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

A modulated squared-sinc function transforms into a translated and rescaled tent. Positive bandwidth fixes the support interval and the scaling factor.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore.fourier_gTent`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore.integral_fejerKernel`
