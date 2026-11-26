# Rare flag BKM limit

## Abstract

Rectangular rare flag logarithmic derivative has the BKM logarithmic asymptotic.

**Theorem 1.1 (The actual resolvent limit).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiRareFlagBKM.rare_flag_logDeriv_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiRareFlagBKM.rare_flag_logDeriv_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite index types iota and kappa, positive definite complex matrices Z and C, and an arbitrary rectangular complex matrix V, set B(delta)=fromBlocks Z 0 0 (delta smul C) and H=fromBlocks 0 V Vᴴ 0. The theorem takes the real trace of Hᴴ times the actual Bochner-integral LogDerivTrace.logDeriv(B(delta),H), divides by 2 log(1/delta), and gives the right-filter limit at delta=0 as Re Tr(Vᴴ Z⁻¹ V).

The proof retains both off-diagonal blocks, diagonalizes Z and C independently, evaluates the finite resolvent pair kernels, and treats coincident eigenvalues before the separated singular branch. Empty carriers and V=0 remain in scope through the finite sums. No normalization, commutation, common eigenbasis, unital output, coefficient equality, or novelty claim is asserted.

This is a reusable support theorem for the rare-reference lower-bound route in the conditional Umegaki problem. It does not construct admissible density-state pairs, prove c0 <= eta_c, establish an all-channel support condition, or settle the external open problem.

**Theorem 1.2 (Positive definiteness of the rare-flag base).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiRareFlagBKM.block_diag_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiRareFlagBKM.block_diag_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota and kappa be arbitrary finite types with decidable equality. For square complex matrices Z on iota and C on kappa, assume Z and C are positive definite and let delta be a strictly positive real number. Then Matrix.fromBlocks Z 0 0 (delta smul C) is positive definite on iota plus kappa. The two index types may differ and may be empty.

This lemma supplies positivity of the base for the rare-flag limit and for both flagged corners in UmegakiFaithfulLowerRatio.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiRareFlagBKM.block_diag_posDef`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiRareFlagBKM.rare_flag_logDeriv_limit`
- Dependency: [D5/S3/Divergence/LogDerivTrace](../../Divergence/LogDerivTrace.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](../Subentropy/UniformIntegrals.md)
