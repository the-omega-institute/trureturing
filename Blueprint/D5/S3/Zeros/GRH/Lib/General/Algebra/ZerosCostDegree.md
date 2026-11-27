# Zeros Cost Degree

## Abstract

Zeros Cost Degree

Schur modules, Weyl lattices, Fischer product, kernel, Gram form, symmetric powers: definitions. High-order vanishing at all points of a complete intersection forces large weighted degree.

**Theorem 1.1 (exists_le_cost_of_vanishing).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Algebra/ZerosCostDegree.exists_le_cost_of_vanishing`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Algebra/ZerosCostDegree.exists_le_cost_of_vanishing` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Give the variable u the cost 1/κ_u. Take at least ∏κ_u distinct points at which each u^{κ_u} agrees with a polynomial whose monomials cost less than 1. Then every f ≠ 0 vanishing to order d at these points has a monomial of cost at least d.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Algebra/ZerosCostDegree.exists_le_cost_of_vanishing`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ColumnLattices](../LinearAlgebra/ColumnLattices.md)
