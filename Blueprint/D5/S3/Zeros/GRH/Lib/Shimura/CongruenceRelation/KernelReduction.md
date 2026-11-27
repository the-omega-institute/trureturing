# Kernel Reduction

## Abstract

Kernel Reduction

Cartier's theorem; finite flat kernel is closure of its generic points. Arithmetic consequences of a good prime: characteristic, uniformiser, coprimality. Reduced isogeny kernels on one-dimensional torsion are cut by powers of one parameter.

**Theorem 1.1 (exists_param_pow_card_eq_zero).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/KernelReduction.exists_param_pow_card_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/KernelReduction.exists_param_pow_card_eq_zero` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let x over k reduce a full y, w = ker(O_E → k) good, T = (E/O_E)ⁿ[w]. Some non-zero t in T reduces to 0. For some additive ν: T → A_x[w](k), each z in A_x[w](B), B local, π: B → k, has τ in ker π with τ^{#ν⁻¹(πz)} = 0 and, if πz = 0, z ≡ 0 mod τ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/KernelReduction.exists_param_pow_card_eq_zero`
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/ComplexComparison](../ThetaGroup/ComplexComparison.md)
