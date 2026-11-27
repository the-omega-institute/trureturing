# Cuspidal At Scalars

## Abstract

Cuspidal At Scalars

Values of Steinberg and cuspidal class functions at field elements, by generating series.

**Theorem 1.1 (moebius_and_greenCuspidal_lsmul).**

Lean statement: `D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalAtScalars.moebius_and_greenCuspidal_lsmul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalAtScalars.moebius_and_greenCuspidal_lsmul` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let F = k[z] have Q elements, g be multiplication by z on an F-space V of dimension m, and N = ∏_{i<m}(X − Q^i). Then 𝟙⁻¹(g) = N(0), and C_η(g) (Hall.greenCuspidal) is −N'(1) times the sum of η over the roots in K of the minimal polynomial of z.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalAtScalars.moebius_and_greenCuspidal_lsmul`
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalSupport](CuspidalSupport.md)
