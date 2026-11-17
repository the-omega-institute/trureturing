# Unit windows of positive zeta zeros

## Abstract

Canonical local counts for the positive zeta spectrum.

**Theorem 1.1 (The positive-spectrum local count).**

Lean statement: `D5/S3/Weil/ZeroData/ZetaSpectrumLocalCount.zetaSpectrum_localCount`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ZetaSpectrumLocalCount.zetaSpectrum_localCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the Riemann hypothesis, the positive zeta spectrum satisfies the local counting estimate with no further assumption. The local_count field of the unconditional canonical Riemann-von Mangoldt theorem bounds the canonical window (t,t+1]. The identity for zetaSpectrum_N and additivity of canonical window counts identify its multiplicity with N(t+1)-N(t), including exactly the upper endpoint and excluding exactly the lower endpoint.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ZetaSpectrumLocalCount.zetaSpectrum_localCount`
- Dependency: [D5/S3/Analytic/Oscillation/GaussianSpectrum](../../Analytic/Oscillation/GaussianSpectrum.md)
- Dependency: [D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum](PositiveOrdinateSpectrum.md)
