# Sum Of Two Squares

## Abstract

Sum Of Two Squares

A totally positive element is a sum of two squares in a quadratic algebra, via Hasse's norm theorem.

**Theorem 1.1 (exists_sq_add_sq_quadraticAlgebra).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/Landherr/SumOfTwoSquares.exists_sq_add_sq_quadraticAlgebra`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/Landherr/SumOfTwoSquares.exists_sq_add_sq_quadraticAlgebra` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let E satisfy StablyUnram, S be a set of finite places of E, and p, q, B ∈ E⁺, p ≠ 0 totally positive, p a unit outside S, q a unit on S ∪ S̄. Then p = x² + y² is solvable in E⁺[X]/(X² − (qp − B²)).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/Landherr/SumOfTwoSquares.exists_sq_add_sq_quadraticAlgebra`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Global/CMNorms](../../ClassField/Global/CMNorms.md)
