# Exact erasure with a Gibbs qubit bath

## Abstract

Exact feasibility and sharp bath heat for reset with a retained qubit record marginal.

**Theorem 1.1 (Rank-two projection bound for the two marginals).**

Lean statement: `D5/S3/Quantum/Decoherence/ExactQubitBathErasure.trace_mul_local_projections_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ExactQubitBathErasure.trace_mul_local_projections_le_three` (`✓ std3`). ∎

*Citation.* Sergey Bravyi (2004). *Requirements for compatibility between local and multipartite quantum states*. DOI: [10.48550/arXiv.quant-ph/0301014](https://doi.org/10.48550/arXiv.quant-ph/0301014). URL: <https://arxiv.org/abs/quant-ph/0301014v2>.

*Commentary.*

The trace pairing of a rank-two projection with the sum of two lifted local rank-one projections is at most three. The finite calculation follows from the eigenvalues 2, 1, 1 and 0 of that sum. It gives the marginal-bias inequality for the repeated spectrum used in the erasure result.

**Theorem 1.2 (Exact Gibbs-bath feasibility and minimum heat).**

Lean statement: `D5/S3/Quantum/Decoherence/ExactQubitBathErasure.gibbs_erasure_threshold_and_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ExactQubitBathErasure.gibbs_erasure_threshold_and_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi (2004). *Requirements for compatibility between local and multipartite quantum states*. DOI: [10.48550/arXiv.quant-ph/0301014](https://doi.org/10.48550/arXiv.quant-ph/0301014). URL: <https://arxiv.org/abs/quant-ph/0301014v2>.

*Commentary.*

A fair bit is recorded by two normalized pure qubit states of absolute overlap s. The independent Gibbs qubit bath has energy gap Δ and bias r=tanh(βΔ/2). A single unitary erases the bit to the prescribed pure state while retaining the average record marginal precisely when s is at most r. The operation permits correlations between the record and bath.

Every admissible erasure increases the bath energy by at least Δs/2. The explicit attaining unitary leaves the bath diagonal with bias r−s. Heat is the increase in the expectation of the specified bath Hamiltonian.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/ExactQubitBathErasure.gibbs_erasure_threshold_and_minimum`
- Truth anchor: `D5/S3/Quantum/Decoherence/ExactQubitBathErasure.trace_mul_local_projections_le_three`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
