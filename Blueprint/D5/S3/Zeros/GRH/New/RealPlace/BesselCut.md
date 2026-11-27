# Bessel Cut

## Abstract

Bessel Cut

Normalise a real-place Bessel function and cut it off. A Bessel function at a real place, an average of a discrete series coefficient that is large at one point, inherits the coefficient's decay, and normalising it and multiplying by a scalar cut-off gives a continuous approximant, close in L² and compactly supported modulo the unipotent group, with an explicit tail bound. Averages of integrable discrete series coefficients over a unipotent group and their decay are known, and the normalisation and scalar cut-off with a tail bound are standard. Related work: Muić, Fourier coefficients of automorphic forms and integrable discrete series, 2015; Miličić, Asymptotic behavior of matrix coefficients of the discrete series, 1977; Wallach, Real Reductive Groups II, 1992.

**Theorem 1.1 (exists_cut_isCutPair).**

Lean statement: `D5/S3/Zeros/GRH/New/RealPlace/BesselCut.exists_cut_isCutPair`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/RealPlace/BesselCut.exists_cut_isCutPair` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Given a peaked Bessel function (HasPeakAt) at x with besselSize x ≤ b^{5(ϱ+1)}, and numerical bounds on b, n, l, there are F, reproduced by convolution with deg·ψ_l, and V such that (F, V) satisfies IsCutPair.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/RealPlace/BesselCut.exists_cut_isCutPair`
- Dependency: [D5/S3/Zeros/GRH/New/DiscreteSeries/BesselExistence](../DiscreteSeries/BesselExistence.md)
- Dependency: [D5/S3/Zeros/GRH/New/RealPlace/OpenCellBound](OpenCellBound.md)
