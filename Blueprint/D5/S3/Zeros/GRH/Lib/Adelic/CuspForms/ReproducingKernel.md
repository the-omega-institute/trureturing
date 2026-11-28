# Reproducing Kernel

## Abstract

Reproducing Kernel

Forms reproduced by a cusp kernel decay rapidly; finite dimension at fixed level. A bounded Poincaré series projected term by term is a form of given level. Poincaré series of the idempotent kernel is a form of level K.

**Theorem 1.1 (exists_kernel_form).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/ReproducingKernel.exists_kernel_form`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/ReproducingKernel.exists_kernel_form` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Poincaré series: for a cusp kernel e, x ∈ G and a level K (IsLevel), there is a K-fixed form k of type e on V with conj k(g) = ∑_{γ∈Γ} e((xγg)_∞)·1_K((xγg)_f) for all g ∈ G.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/ReproducingKernel.exists_kernel_form`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/CuspStep](CuspStep.md)
