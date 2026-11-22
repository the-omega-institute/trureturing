# The diagonal budget for decoding through quantum memory

## Abstract

Finite CPTP memory imposes a scalar budget on flat phase records.

**Theorem 1.1 (An effect family is bounded by its summed diagonal).**

Lean statement: `D5/S3/Quantum/PureState/QuantumMemoryBudget.sum_scores_le_of_effect_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/QuantumMemoryBudget.sum_scores_le_of_effect_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive effect, take its positive matrix square root and apply the Euclidean triangle inequality over carrier coordinates to the square root acting on the signal. The norm of each column is the square root of the corresponding effect diagonal. A second Euclidean triangle inequality, this time over labels, bounds the sum of scores by the square of the amplitude sum weighted by √dᵢ, where dᵢ is the sum of the effect diagonals at coordinate i.

**Theorem 1.2 (Every common CPTP encoder and output POVM yields a feasible profile).**

Lean statement: `D5/S3/Quantum/PureState/QuantumMemoryBudget.exists_success_le_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/QuantumMemoryBudget.exists_success_le_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider normalized finite signals with the same nonnegative amplitudes t and unit-modulus phases for each label. Pull back each output POVM effect and use the spectral supplier's score-preserving compression. The compressed effects sum to at most the identity, and each trace is bounded by the corresponding output effect trace. Their summed diagonal has entries in [0,1] and total mass at most the memory dimension M. For uniform labels, the success is at most the square of the profile value divided by the number of labels. This upper bound only requires unit-modulus phases.

## References

- Truth anchor: `D5/S3/Quantum/PureState/QuantumMemoryBudget.exists_success_le_profile`
- Truth anchor: `D5/S3/Quantum/PureState/QuantumMemoryBudget.sum_scores_le_of_effect_family`
- Dependency: [D5/S3/Quantum/PureState/DistillationProfile](DistillationProfile.md)
- Dependency: [D5/S3/Quantum/PureState/PhaseRecordSpectralMemory](PhaseRecordSpectralMemory.md)
