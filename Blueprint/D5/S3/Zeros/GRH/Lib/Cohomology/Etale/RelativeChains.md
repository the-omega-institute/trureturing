# Relative Chains

## Abstract

Relative Chains

Relative cohomology of pairs of functors; locally zero sections, excision, transfer.

**Theorem 1.1 (excision).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/RelativeChains.excision`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/RelativeChains.excision` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Excision: if u: V' → V is a monomorphism and u(V') ∪ U is dense in V for the coefficient F, then ℤ[V']/ℤ[u⁻¹U] → ℤ[V]/ℤ[U] induces bijections on Ext^n(·, F) for all n.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/RelativeChains.excision`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Relations](Relations.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/CupProduct](../Hodge/CupProduct.md)
