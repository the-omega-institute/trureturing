# Weak recording with local baths

## Abstract

A cost bound for weak records under local bath steps and collective reversible control.

**Theorem 1.1 (The cost of several readable coordinates).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/LocalBathWeakRecording.recording_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/LocalBathWeakRecording.recording_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

Each conditional register law starts uniform. A scheduled bath uses the same two-state transition probabilities in all fibers of one bit and satisfies an edgewise charge bound. The protocol may apply joint reversible permutations in either branch. The cost multiplies the branch-averaged transition activity by the branch-averaged certified edge charge. The logarithmic specialization evaluates the two fluxes at the input law of the step. Total bath variation controls the largest departure from uniform, and the single-bit geometry bounds the Euclidean speed from the two bath costs. Orthogonality of the coordinate signs gives a lower coefficient of R/2 for the squared common Bayes bias in the weak-recording limit at fixed dimension.

## References

- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/LocalBathWeakRecording.recording_bound`
- Dependency: [D5/S3/Quantum/Information/RecordWriting/TwoRegister](TwoRegister.md)
- Dependency: [D5/S3/TotalVariation/Pinsker](../../../TotalVariation/Pinsker.md)
