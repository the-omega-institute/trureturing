# Shear Invariance

## Abstract

Shear Invariance

Cut-off ramified character: periodic, of norm one on units, locally constant. The cut-off inverse character is multiplicative on integers. Standard ramified data given by determinants; they are partners and Schwartz-Bruhat. Local Gauss sum from the residue ring; three-block integral frames and standard data. Invariance under block translations implies invariance under shears of standard data.

**Theorem 1.1 (shear_invariant).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/GaussSum/ShearInvariance.shear_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/GaussSum/ShearInvariance.shear_invariant` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let s be integral, u a column, r a row, su = 0, ru = 0. If the linear form Λ is invariant, on a space M of Schwartz–Bruhat functions, under all y ↦ y + u·z·s·y, it agrees on Ψ_s = stdColDatum and on Ψ_s(y + u·r·y) when both lie in M.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/GaussSum/ShearInvariance.shear_invariant`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartnerAlgebra](../../General/LinearAlgebra/PartnerAlgebra.md)
