# Fourier comparison with a signed density

## Abstract

Ramp approximation bounds probability distribution functions against signed densities through their Fourier difference.

**Theorem 1.1 (A Fourier bound for a signed comparison density).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/StatLeanSignedSmoothing.abs_measure_Iic_sub_densityCDF_le_charFun`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/StatLeanSignedSmoothing.abs_measure_Iic_sub_densityCDF_le_charFun` (`✓ std3`). ∎

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Compare the distribution function of a probability measure with the integral of an integrable real function. The comparison function may have either sign. A bound on its absolute integral over intervals controls the ramp approximation error; a weighted characteristic-function difference controls the smoothed error.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanSignedSmoothing.abs_measure_Iic_sub_densityCDF_le_charFun`
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore](StatLeanFourierCore.md)
