# Adelic Ring Defs

## Abstract

Adelic Ring Defs

Generalised inverses, factorisation through a column space, ye + bx = 1 over a field. Linear duality: vectors agreeing under all annihilating functionals agree modulo two subspaces. Integral vectors and matrices over a subring, generalised index, lattices, congruence levels.

**Theorem 1.1 (exists_mulVec_eq_of_annihilator).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/AdelicRingDefs.exists_mulVec_eq_of_annihilator`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/AdelicRingDefs.exists_mulVec_eq_of_annihilator` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let s, s' be sets of column indices. If every linear form l killing the columns of P in s and those of P' in s' has l(PX) = l(P'Y), then Px = P'y for some x equal to X off s and y equal to Y off s'.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/AdelicRingDefs.exists_mulVec_eq_of_annihilator`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Analysis/ZpowSum](../Analysis/ZpowSum.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ExtendColumns](ExtendColumns.md)
