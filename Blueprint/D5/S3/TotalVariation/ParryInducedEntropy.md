# Entropy of the zero-section return

## Abstract

The entropy of the native bilateral Parry return system.

**Theorem 1.1 (Kolmogorov–Sinai entropy of the Parry induced map).**

Lean statement: `D5/S3/TotalVariation/ParryInducedEntropy.actual_return_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryInducedEntropy.actual_return_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same bilateral Parry coding and stationary source, use the actual first-return transformation and the normalized measure on the zero section. Its full Kolmogorov–Sinai entropy is the Shannon entropy of the return duration distribution, in nats per return. Duration d has probability p^d for d from 1 through k, with p the reciprocal Parry root. The entropy also equals -log p divided by the stationary probability of the zero section. The expected duration equals the normalizing sum of the stationary suffix law, which is the reciprocal of the zero-section mass.

The product cylinder law makes the entropy of the first n durations exactly n times the one-duration entropy, giving the lower bound. For the upper bound, take a coordinate window of radius m at induced iterates 0 through n-1, starting at the initial section point. The original m negative coordinates and the first n + m durations determine all these windows. Each duration reconstructs a run of ones and its closing zero. The entropy cost of the negative coordinates is at most m log 2, regardless of their dependence on the future returns.

Dividing the window entropy by n and passing to the limit bounds every finite coordinate window by the same duration entropy. The finite windows together generate the bilateral measurable space. The increasing-partition bound therefore applies to the supremum over all finite measurable partitions.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryInducedEntropy.actual_return_entropy`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/Bernoulli](../Entropy/KolmogorovSinai/Bernoulli.md)
- Dependency: [D5/S3/TotalVariation/ParryFirstReturn](ParryFirstReturn.md)
