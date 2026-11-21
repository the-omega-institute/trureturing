# Inverse Fourier support at the directional half-width

## Abstract

An entire function with a square-integrable real restriction has inverse Fourier support bounded by its directional exponential type.

**Theorem 1.1 (Almost-everywhere support of the inverse Fourier class).**

Lean statement: `D5/S3/Fourier/InverseFourierSupport.inverse_fourier_L2_support`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/InverseFourierSupport.inverse_fourier_L2_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be entire with square-integrable real restriction. Suppose its norm is bounded by C times (1 + |z|) to the power m times exp(a |Im z|). The L2 inverse of the function xi mapped to F(2 pi xi) vanishes almost everywhere where |t| exceeds a.

Multiplying F by sinc(epsilon z) to the power m + 2 gives inverse-square decay in each horizontal strip. Cauchy integration on rectangles shifts the angular inverse integral with phase exp(i t z) into the upper half plane for the positive tail. Reflection gives the negative tail. Each regularized inverse is supported at half-width a + (m + 2) epsilon. Classical inversion and forward L1/L2 agreement identify this inverse with the L2 inverse. The regularized restrictions converge in L2 by dominated convergence, and an almost-everywhere convergent subsequence of the inverses gives the limiting half-width a.

## References

- Truth anchor: `D5/S3/Fourier/InverseFourierSupport.inverse_fourier_L2_support`
- Dependency: [D5/S3/Fourier/InfiniteSincProduct](InfiniteSincProduct.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/LineFourier](../Weil/ZetaGamma/FormCore/LineFourier.md)
