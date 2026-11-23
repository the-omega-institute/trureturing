# Gaussian limit for occupancy with discarded throws

## Abstract

The count of distinct ordinary bins hit has a standard Gaussian weak limit after exact row standardization.

**Theorem 1.1 (Gaussian limit of literal occupancy).**

$$\forall (k: \mathbb{N}), 2 \leq k \implies \operatorname{Tendsto}\left((N: \mathbb{N} \mapsto \operatorname{literalLaw}\left(k, N\right)), atTop, \operatorname{nhds}\left(\operatorname{gaussianReal}\left(0, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.exact_occupancy_normal_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Row N has N plus one ordinary bins and N independent throws. The ordinary-bin masses are one divided by k times the number of bins, and each remaining mass belongs to the discard outcome. Standardization uses the expectation and variance under the product measure in that row. The proof telescopes the conditional characteristic-function comparisons and applies Lévy continuity.

## References

- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.exact_occupancy_normal_limit`
- Dependency: [D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic](Characteristic.md)
