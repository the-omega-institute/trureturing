# Rank-two rational extensions for equal spectra

## Abstract

A rational rank bound for qubit marginals with equal spectra.

**Theorem 1.1 (A rational joint state of rank at most two for equal determinants).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitEqualSpectrumRank.rational_endpoint_rank_le_two_of_equal_det`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/RationalQubitEqualSpectrumRank.rational_endpoint_rank_le_two_of_equal_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two positive semidefinite trace-one qubit marginals with rational real and imaginary parts and equal determinants admit a positive semidefinite joint matrix of rank at most two with rational real and imaginary parts.

Subtract half the identity from each marginal. The two centered matrices square to the same scalar times the identity. If the scalar is nonzero, divide their tensor product by it to obtain a traceless Hermitian involution. The projection onto its positive eigenspace has trace and rank two. Compress the left marginal tensored with the identity by this projection. The centered traces vanish, while the trace of the left marginal times its centered part is twice the common scalar. The two partial traces recover the given marginals. If the scalar is zero, both marginals are half the identity. The equal mixture of the two matching basis words gives the required state.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitEqualSpectrumRank.rational_endpoint_rank_le_two_of_equal_det`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity](RationalQubitPurity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
