# Worst-direction gain of quantum process tomography

## Abstract

The least realignment singular value is attained by an actual pair of finite quantum channels.

**Theorem 1.1 (The exact weakest gain).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain.leastRealignmentSV_sq_isLeast_cptp_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain.leastRealignmentSV_sq_isLeast_cptp_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gurvir Singh (2026). *Ancilla Assisted Quantum Process Tomography using Bound entangled states*. URL: <https://arxiv.org/abs/2605.19182v3>.

*Commentary.*

For a square Hermitian probe, the minimum ratio of squared output Hilbert–Schmidt distance to squared unnormalized Choi Hilbert–Schmidt distance equals the square of the least realignment singular value. The contraction of a Hermitian probe preserves the adjoint involution on input slices. A least singular direction can therefore be chosen Hermitian. A positive and negative perturbation of the strictly positive depolarizing Choi matrix realizes it by two distinct trace-preserving completely positive maps into a qubit.

**Theorem 1.2 (A marginal-dependent reconstruction bound).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain.exists_cptp_pair_weighted_ppt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain.exists_cptp_pair_weighted_ppt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Horodecki and Paweł Horodecki (1999). *Reduction criterion of separability and limits for a class of protocols of entanglement distillation*. DOI: [10.1103/PhysRevA.59.4206](https://doi.org/10.1103/PhysRevA.59.4206). URL: <https://arxiv.org/abs/quant-ph/9708015v2>.

*Commentary.*

For a trace-one PPT probe written in an eigenbasis of its positive second marginal, the same attaining channel pair obeys the upper bound from the marginal spectrum. The construction uses actual channel pairs for each probe covered by the reduction inequality.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain.exists_cptp_pair_weighted_ppt`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PPTOperationalGain.leastRealignmentSV_sq_isLeast_cptp_gain`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction](../Entanglement/Witness/PPTWeightedReduction.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography](PauliDiagonalPPTTomography.md)
