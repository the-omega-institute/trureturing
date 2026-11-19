# Compatibility of the integral and L² Fourier transforms

## Abstract

The integral and L² Fourier transforms agree for integrable square-integrable complex functions on the real line, in Mathlib's frequency convention with kernel exp(-2*pi*i*x*xi).

**Theorem 1.1 (Almost-everywhere agreement).**

Lean statement: `D5/S3/Analytic/Fourier/RawFourierL2.raw_fourier_ae_eq_L2`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/RawFourierL2.raw_fourier_ae_eq_L2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral transform is continuous, and the L² transform is locally integrable. Pairing with compactly supported smooth tests gives the same integrals by Fourier duality and Mathlib's identification of the L² transform with the tempered-distribution transform. The test integrals imply almost-everywhere equality.

**Theorem 1.2 (Preservation of the L² seminorm).**

Lean statement: `D5/S3/Analytic/Fourier/RawFourierL2.raw_fourier_eLpNorm_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/RawFourierL2.raw_fourier_eLpNorm_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Almost-everywhere agreement transfers the seminorm to the L² transform, where the Fourier linear isometry preserves it.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/RawFourierL2.raw_fourier_ae_eq_L2`
- Truth anchor: `D5/S3/Analytic/Fourier/RawFourierL2.raw_fourier_eLpNorm_eq`
