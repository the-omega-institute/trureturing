# Mean-square error on dyadic height intervals

## Abstract

Mean-square error for a Dirichlet truncation of zeta

**Theorem 1.1 (Uniform error to the right of the critical line).**

Lean statement: `D5/S3/Weil/ZetaTruncationMeanSquare.dyadic_truncation_mean_square`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaTruncationMeanSquare.dyadic_truncation_mean_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a, b, u and T with 1/2 < a ≤ u ≤ b and T ≥ 2, the bound uses the sum of n^(−s) for 1 ≤ n ≤ ceil(T), evaluated at s = u + it. Integrate the squared error over T − 1 ≤ |t| ≤ 2T + 1. The squared error is integrable there, and its integral is bounded by (250 + 2(b+3)^2 π/(4a)) times T^(2−2a).

The exact Euler–Maclaurin identity separates the explicit correction and its Bernoulli integral. Substituting x = exp(v) in that integral gives an angular Fourier transform of a bounded sawtooth times exp(−uv), restricted to v > log(ceil(T)). Plancherel bounds the squared integral of the transform on the real line. On the indicated height band, the remaining factor |s|² costs at most a constant times T².

## References

- Truth anchor: `D5/S3/Weil/ZetaTruncationMeanSquare.dyadic_truncation_mean_square`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/LineFourier](ZetaGamma/FormCore/LineFourier.md)
