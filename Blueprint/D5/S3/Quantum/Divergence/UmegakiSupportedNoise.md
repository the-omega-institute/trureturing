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

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiSupportedNoise.tendsto_finiteTraceLogRelativeEntropy_of_noise`
- Dependency: [D5/S3/Quantum/Divergence/AlphaZAffine/Result](AlphaZAffine/Result.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation](../Measurements/BroadcastingChannelExtremaRefutation.md)
