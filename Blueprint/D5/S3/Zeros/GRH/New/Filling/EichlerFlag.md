# Eichler Flag

## Abstract

Eichler Flag

Link of two frames, Gram discriminant g(γ); basis of the marked unimodular lattice. Abstract systems of positive kernels: products, semicontinuity, floor-by-floor sieve bound. Eichler maps along a frame vector lie in the Bessel unipotent group; character value.

**Theorem 1.1 (exists_mem_besselU_eq_eichlerMap).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/EichlerFlag.exists_mem_besselU_eq_eichlerMap`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/EichlerFlag.exists_mem_besselU_eq_eichlerMap` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let x = r∑_b j_b f_b with j_b = 0 for b ≥ a, and m = h(v, ·) vanish at f_b for b < a. The Eichler map 1 + x h(v, ·) − (v + τh(v,v)x) h(x, ·) is an element u of 𝖴 with σ(u) = r∑_b j_b m(f_{b+1}); f is the frame, σ = simpleRootSum, τ = TraceOne.τ has trace 1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/EichlerFlag.exists_mem_besselU_eq_eichlerMap`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bruhat/BigCell](../../Lib/DiscreteSeries/Bruhat/BigCell.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Topology/LocalDefs](../../Lib/General/Topology/LocalDefs.md)
