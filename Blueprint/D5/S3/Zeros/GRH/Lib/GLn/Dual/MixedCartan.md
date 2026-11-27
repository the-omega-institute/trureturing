# Mixed Cartan

## Abstract

Mixed Cartan

Integral isometric Cartan component of a Weyl module tensor a dual Weyl module.

**Theorem 1.1 (nonempty_mixedCartanEmbedding).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GLn/Dual/MixedCartan.nonempty_mixedCartanEmbedding`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GLn/Dual/MixedCartan.nonempty_mixedCartanEmbedding` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Duality for Weyl lattices: for all column counts kp and km, a map PolyRep.MixedCartanEmbedding exists from the lattice with column counts kp_τ(i) + km_τ(|n| − i) to Δ_kp ⊗ Δ_km, that is, an equivariant integral isometry with integral left inverse sending ev₁ to ev₁ ⊗ ev_{w₀}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GLn/Dual/MixedCartan.nonempty_mixedCartanEmbedding`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/DeltaForms](../../Adelic/CuspForms/DeltaForms.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/Branching/Branching](../Branching/Branching.md)
