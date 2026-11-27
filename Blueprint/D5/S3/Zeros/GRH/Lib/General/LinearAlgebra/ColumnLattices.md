# Column Lattices

## Abstract

Column Lattices

Smith normal form over rings that are valuation rings up to idempotents. Integral and unimodular matrices, congruence subgroups of unitary groups: basic lemmas. Inverse transpose, adjoints of spherical Hecke operators, commutativity by Gelfand's trick. Basic facts on integral lattices, column spans and generalised index over a subring.

**Theorem 1.1 (liftIntegralFn_mul).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ColumnLattices.liftIntegralFn_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ColumnLattices.liftIntegralFn_mul` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For π : R → B, a ∈ GL_n(R), b ∈ GL_m(R) and an m × n matrix M over A, the value of liftIntegralFn π f at bMa equals the value at M of the lift of X ↦ f(π(b)Xπ(a)).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ColumnLattices.liftIntegralFn_mul`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Hecke/HeckeBasic](../../Adelic/Hecke/HeckeBasic.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/AdelicRingDefs](AdelicRingDefs.md)
