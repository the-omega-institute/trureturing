# Row Balanced

## Abstract

Row Balanced

Roots of unity give a tame class; lattices in columns read above ℓ. Local duality bounds Ribet cocycles' distance from crystalline by the dual lattice's defect. Rows are balanced: local conditions and mirror scalar within explicit bound.

**Theorem 1.1 (eventually_isBalanced).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/RowBalanced.eventually_isBalanced`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/RowBalanced.eventually_isBalanced` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For a row R of rank n, a chosen place w off ℓ and all large O, some lattice u is balanced (IsBalanced) for Z_f above ℓ, and β plus v(det(u(σ) − 1)) for σ = σ_w, σ_w^{−c} (σ_w a tame generator at w) has normalised length ≤ 10fn·cr_ℓ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/RowBalanced.eventually_isBalanced`
- Dependency: [D5/S3/Zeros/GRH/New/Lift/ExponentTheorems](../Lift/ExponentTheorems.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/CrystallineRank](CrystallineRank.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/TwistTheorem](TwistTheorem.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/ValueFamilies](ValueFamilies.md)
