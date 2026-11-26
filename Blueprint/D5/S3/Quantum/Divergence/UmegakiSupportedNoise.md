# Umegaki entropy under supported density noise

## Abstract

Support containment and a one-sided data-processing bound yield convergence of finite Umegaki entropy.

**Theorem 1.1 (One-sided supported entropy limit).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiSupportedNoise.tendsto_finiteTraceLogRelativeEntropy_of_noise`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiSupportedNoise.tendsto_finiteTraceLogRelativeEntropy_of_noise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the first density state be supported inside the second. As the weight tends to zero from above, each state mixes with its own fixed density noise. The mixtures must eventually have support containment and finite entropy at most the original finite entropy.

The self-log term converges by continuity. The supported cross-log comparison supplies the required lower limit by bounding the second mixture with a positive shift of the original second state. The eventual upper bound then gives convergence of the finite divergence.

**Theorem 1.2 (Fixed-weight supported logarithm limit).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiSupportedNoise.supported_log_shift_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiSupportedNoise.supported_log_shift_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2024). *Log-majorization and matrix norm inequalities with application to quantum information*. DOI: [10.1007/s44146-024-00142-w](https://doi.org/10.1007/s44146-024-00142-w). URL: <https://arxiv.org/abs/2402.16067>.

*Commentary.*

If H is positive semidefinite and W kills its kernel, then W times the log of H shifted by a positive multiple of the identity tends to W times the supported log of H. The regularization term carrying only the shift weight tends to zero.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiSupportedNoise.supported_log_shift_tendsto`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiSupportedNoise.tendsto_finiteTraceLogRelativeEntropy_of_noise`
- Dependency: [D5/S3/Quantum/Divergence/AlphaZAffine/Result](AlphaZAffine/Result.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
