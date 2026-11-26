# Interlacing Cone

## Abstract

Interlacing Cone

Cyclic interlacing cone volume as a signed sum over permutations, via determinant of indicators. The cyclic interlacing cone fills the share of one flag in volume.

**Theorem 1.1 (prod_mul_volume_inter_slab).**

Lean statement: `D5/S3/Zeros/GRH/New/TwistedHecke/InterlacingCone.prod_mul_volume_inter_slab`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/TwistedHecke/InterlacingCone.prod_mul_volume_inter_slab` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let P > 1, q = P^N, and let Ω be a set such that permStep v P 1 ν lies in Ω exactly when ν lies in pieriCone v P. Then ∏_{l=1}^{k} (q^l − 1)/(q − 1) · vol(Ω ∩ Σ) = vol(Σ), for Σ = slab k D.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/TwistedHecke/InterlacingCone.prod_mul_volume_inter_slab`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HaarUnique](../../Lib/General/LinearAlgebra/HaarUnique.md)
