# Cuspidal Support

## Abstract

Cuspidal Support

Cuspidal class functions vanish unless the characteristic polynomial is a prime power.

**Theorem 1.1 (exists_charpoly_eq_pow).**

Lean statement: `D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalSupport.exists_charpoly_eq_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalSupport.exists_charpoly_eq_pow` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Over a finite field k, if F is cuspidal (Hall.IsCuspidal) and does not vanish at the class of an endomorphism g, then the characteristic polynomial of g is a power of an irreducible polynomial.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalSupport.exists_charpoly_eq_pow`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ValuedMatrix](../../General/LinearAlgebra/ValuedMatrix.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Green/FrobeniusOrbits](FrobeniusOrbits.md)
