# Hecke Basic

## Abstract

Hecke Basic

Abstract Hecke operators of (G,K): coset sums, functoriality, composition as convolution.

**Theorem 1.1 (heckeFun_heckeFun).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/Hecke/HeckeBasic.heckeFun_heckeFun`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/Hecke/HeckeBasic.heckeFun_heckeFun` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let f, f' be nonzero at finitely many representatives of G/K, f right K-invariant, v fixed by K. Then f'(fv) = (f' ∗ f)v for the action heckeFun, where (f' ∗ f)(x) = ∑ f'(g)f(g⁻¹x) over the representatives g.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/Hecke/HeckeBasic.heckeFun_heckeFun`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartialDerivComm](../../General/LinearAlgebra/PartialDerivComm.md)
