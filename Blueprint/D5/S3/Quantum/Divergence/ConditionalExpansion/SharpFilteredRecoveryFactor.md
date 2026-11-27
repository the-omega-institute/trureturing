# Sharp filtered recovery factor

## Abstract

A complementary depolarizing filter defeats every proposed conditional factor below d².

**Theorem 1.1 (Strict witness below the dimension-square factor).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/SharpFilteredRecoveryFactor.sharp_factor_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/SharpFilteredRecoveryFactor.sharp_factor_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every C < d² and every finite input type of size d ≥ 2, there is a small Bell eigenvalue a and a filtered channel N with act N equal to filterAction of the Datta–Holevo complementary depolarizing filter. Every finite exact heralded recovery of N has weight at most a, while the conditional ratio infimum is strictly greater than C a for the orthogonal test and for every γ ≥ 1 in the full test.

The algebraic choice of a uses the normalized inverse-marginal harmonic parameter and proves sharpness of the universal d² factor. The conditional expansion coefficient is Hirche–George–Nuradha–Wilde, arXiv:2608.27171v1, Eq. (2.42). The filter family follows Datta–Holevo, arXiv:quant-ph/0510145, §3, Eqs. (11) and (16). The related recovery duality is Bény–Oreshkov, arXiv:1103.0649v3, Theorem 2.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/SharpFilteredRecoveryFactor.sharp_factor_witness`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit](BellKernelLimit.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap](FilteredChannelConditionalGap.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausLeftInverseNecessity](../../Recovery/KrausLeftInverseNecessity.md)
