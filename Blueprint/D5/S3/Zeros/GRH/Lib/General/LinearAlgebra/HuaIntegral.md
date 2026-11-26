# Hua Integral

## Abstract

Hua Integral

Real Heisenberg bicharacter, Gaussian vacuum, creation and annihilation operators, Lie algebra action. Euclidean volume normalised by Gaussian integral one; products and powers. Principal minors: norm bound, multiplicativity, Jacobi's complementary minor theorem. Upper bound for Hua's determinant integral; beta-type integrals.

**Theorem 1.1 (hua_integral_le).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HuaIntegral.hua_integral_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HuaIntegral.hua_integral_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Hua's integral bound: for M positive definite and S invertible of size k, c ≥ 0, r ≥ k, y_i = x_iS + a_i, the integral of c|det(M + Σ_{i∈s} y_iᴴy_i)|^{−(|s|+r)} over rows x_i ∈ ℂ^k, i ∈ s, is at most c(π^k/(k!|det S|²))^{|s|}|det M|^{−r}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HuaIntegral.hua_integral_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Groups/ValuationPair](../Groups/ValuationPair.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HaarUnique](HaarUnique.md)
