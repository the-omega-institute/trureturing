# Central Convolution

## Abstract

Central Convolution

Central projections of a group algebra act as orthogonal projections; convolution contracts.

**Theorem 1.1 (sum_norm_conv_le).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Groups/CentralConvolution.sum_norm_conv_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Groups/CentralConvolution.sum_norm_conv_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Convolution with a central self-adjoint idempotent e of ℂ[G], along a homomorphism φ : G → H of finite groups, is a contraction of ℓ²(H, V): ∑_s ‖∑_t e(t) f(φ(t)⁻¹ s)‖² ≤ ∑_s ‖f(s)‖².

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Groups/CentralConvolution.sum_norm_conv_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Green/LabelIdempotents](../../LocalGL/Green/LabelIdempotents.md)
