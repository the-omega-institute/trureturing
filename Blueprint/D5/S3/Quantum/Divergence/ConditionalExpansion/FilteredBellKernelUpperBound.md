# Bell-kernel upper bound for filtered channels

## Abstract

The inverse filter determines the Bell-kernel upper bound on conditional expansion.

**Theorem 1.1 (Upper bound from the inverse marginal).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound.filtered_channel_bell_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound.filtered_channel_bell_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a positive definite filter on A ⊗ E normalized by Tr_E G / e = I, with d = dim A ≥ 2 and e = dim E > 0. Set M = Tr_A(G⁻¹) / d. The conditional expansion of the filtered channel is at most Tr(M⁻¹) / e for every hockey-stick parameter γ ≥ 1, with either choice of orthogonality restriction. The kernel projection of the amplified output of the Bell complement yields this upper bound through the padded Bell pairs.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound.filtered_channel_bell_upper_bound`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit](BellKernelLimit.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap](FilteredChannelConditionalGap.md)
