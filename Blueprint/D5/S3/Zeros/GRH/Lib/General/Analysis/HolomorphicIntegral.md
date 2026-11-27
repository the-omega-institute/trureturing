# Holomorphic Integral

## Abstract

Holomorphic Integral

Holomorphic implies analytic in several variables; analyticity of parameter integrals. Cauchy estimate, holomorphy of parametric integrals, Mellin integrals on a strip.

**Theorem 1.1 (mellin_analytic_on_strip).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Analysis/HolomorphicIntegral.mellin_analytic_on_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Analysis/HolomorphicIntegral.mellin_analytic_on_strip` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let N > 0 be measurable, T·N^t integrable and the integral of |T|·N^s finite. Then ∫ T·N^z dμ converges absolutely and is continuous for real z in [s, t], and is real-analytic on (s, t).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Analysis/HolomorphicIntegral.mellin_analytic_on_strip`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Analysis/OstrowskiTaussky](OstrowskiTaussky.md)
