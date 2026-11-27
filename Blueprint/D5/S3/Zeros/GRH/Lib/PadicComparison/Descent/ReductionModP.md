# Reduction Mod P

## Abstract

Reduction Mod P

p-adic tests, their tilts, Witt and completion functors, base change of coefficients. Locally constant functions on Spec, flatness over Bezout domains, torsion-free tensors, Witt vectors.

**Theorem 1.1 (witt_reduction_spec).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/ReductionModP.witt_reduction_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/ReductionModP.witt_reduction_spec` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let S be a perfect algebra over a domain M of characteristic p. Then the zeroth coordinate W(S) → S is reduction modulo p, W(S) is p-torsion-free and p-complete, and x lies in p^k W(S) exactly when its first k coordinates vanish.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/ReductionModP.witt_reduction_spec`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/MultivariateHensel](../../General/Algebra/MultivariateHensel.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineTests](../Crystalline/CrystallineTests.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/ThetaKernel](../../PadicHodge/PeriodRings/ThetaKernel.md)
