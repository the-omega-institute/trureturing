# Lattice Complement

## Abstract

Lattice Complement

Integral finite adeles of a CM field with 5040th roots of unity: adelic-ring axioms. Adelic index of a field element equals its absolute norm (product formula). Saturation, indices, discriminant of an orthogonal complement in a unimodular adelic lattice.

**Theorem 1.1 (jacobi_perp_discriminant).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Algebra/LatticeComplement.jacobi_perp_discriminant`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Algebra/LatticeComplement.jacobi_perp_discriminant` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let J be unimodular, F integral, n primitive, FᴴJn = 0 with complementary sizes, N = Gram(F|p) plus c on the p-block, and F left invertible or [det N] ≠ 0. Then n^⊥ ⊆ span F and [det nᴴ(J + c⁻¹JppᴴJ)n]·i²·[c]^|ρ| = [det N], i = [{y | Fy integral} : R^σ].

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Algebra/LatticeComplement.jacobi_perp_discriminant`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Witt/MaximalCompact](../../Adelic/Witt/MaximalCompact.md)
