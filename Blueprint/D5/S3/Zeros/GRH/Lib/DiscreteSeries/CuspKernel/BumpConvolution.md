# Bump Convolution

## Abstract

Bump Convolution

Convolution with compactly supported smooth functions is smooth; derivatives fall on the bump.

**Theorem 1.1 (hasDerivAt_smear).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BumpConvolution.hasDerivAt_smear`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BumpConvolution.hasDerivAt_smear` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Derivatives of a convolution fall on the test function: if a curve γ in U(diag ε) has γ'(t) = γ(t)X, then smear α along γ has derivative at t the value at γ(t) of smear (Xα), Xα the right derivative.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BumpConvolution.hasDerivAt_smear`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/RegularRepL2](../Haar/RegularRepL2.md)
