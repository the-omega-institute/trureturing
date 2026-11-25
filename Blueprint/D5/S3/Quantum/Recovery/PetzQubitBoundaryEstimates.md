# Logistic endpoint evaluation with a correlated pair

## Abstract

One correlated pair among three logistic modes improves the endpoint evaluation bound.

**Theorem 1.1 (Three-mode evaluation bound).**

Lean statement: `D5/S3/Quantum/Recovery/PetzQubitBoundaryEstimates.close_pair_weighted_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzQubitBoundaryEstimates.close_pair_weighted_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let three real frequencies carry arbitrary complex coefficients. If the logistic correlation between the first slot and either other slot is at least one fifth, the logistic weighted squared amplitude is integrable and its integral multiplied by 8/3 bounds the squared endpoint amplitude. The frequency values may coincide.

The square root of the correlation Gram supplies three unit vectors. The trace represents evaluation on their rank-one projectors. The Hermitian part of an outer product constructed from an orthogonal complement is perpendicular to all three projectors. Subtracting its component from the identity gives a trace representer with squared Hilbert–Schmidt norm at most 8/3.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzQubitBoundaryEstimates.close_pair_weighted_evaluation`
- Dependency: [D5/S3/Quantum/Recovery/PetzMixedBoundaryEvaluation](PetzMixedBoundaryEvaluation.md)
