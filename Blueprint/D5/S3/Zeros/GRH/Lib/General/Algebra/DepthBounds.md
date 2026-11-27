# Depth Bounds

## Abstract

Depth Bounds

Coefficients of substituted p-adic series; bounds by products over columns; lowest terms.

**Theorem 1.1 (coeff_subst_linearSeries).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Algebra/DepthBounds.coeff_subst_linearSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Algebra/DepthBounds.coeff_subst_linearSeries` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For g ∈ ℂ_p[[t]] and a linear form ∑ c_x z_x in finitely many variables, the coefficient of z^D in g(∑ c_x z_x) is (∏ c_x^{D_x}) · |D|! · g_{|D|} / ∏ D_x!, with |D| the total degree and g_n the n-th coefficient of g.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Algebra/DepthBounds.coeff_subst_linearSeries`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/JetChainRule](JetChainRule.md)
