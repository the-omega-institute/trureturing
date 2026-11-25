# Fixed-marginal noise for ordinary Petz recovery

## Abstract

Environmental replacement preserves both retained marginals, contracts the supported relative entropy loss, and preserves strict ordinary Petz scores at small positive noise.

**Theorem 1.1 (Contraction of the supported entropy loss).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise.noise_loss_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise.noise_loss_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each input, mix its joint state with the product of its own retained marginal and the normalized identity on the environment. The source is supported inside the reference, and the retained reference marginal is faithful. The entropy loss is the full trace-log relative entropy minus the trace-log relative entropy of the retained pair.

The replacement pair has exactly the retained entropy. Its uniform environment makes the trace-log expression a sum of identical scaled blocks. Joint convexity bounds the noisy entropy by the two weighted entropies, and the retained term is fixed for each input. The resulting loss is nonnegative and bounded above by the original loss times one minus the noise weight, including both endpoints.

**Theorem 1.2 (Persistence of a strict ordinary Petz score).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise.exists_strict_score_noise`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise.exists_strict_score_noise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The score divides the unhalved squared trace norm of the ordinary Petz reconstruction error by the supported entropy loss. At any positive original loss and any real threshold strictly below the score, a weight strictly between zero and one preserves the strict inequality. Both original marginals are fixed. The noisy joint reference is faithful and contains the support of the noisy source. The noisy source is faithful whenever its retained marginal is faithful. The noisy loss is positive and satisfies the contraction above.

Fixing the marginals fixes the middle factor of the Petz map. Continuity of the square root on the joint reference and continuity of the supported entropy along the mixture give right continuity of the score at zero. The replacement term gives the noisy reference a strictly positive spectral floor.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise.exists_strict_score_noise`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise.noise_loss_contract`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](../../Divergence/ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportedTraceLog](../../Divergence/SupportedTraceLog.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiSupportedNoise](../../Divergence/UmegakiSupportedNoise.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinementPetz](../BKMFlagRefinementPetz.md)
