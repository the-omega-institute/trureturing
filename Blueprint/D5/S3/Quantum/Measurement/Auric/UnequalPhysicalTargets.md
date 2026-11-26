# Fixed-law states and their coherent record

## Abstract

Fixed-law states and their coherent record

**Theorem 1.1 (The Born law of the normalized input).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.input_recordLaw`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.input_recordLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An admissible state is P/r for a rank-r Hermitian projection with fiber trace r q_j and constant diagonal on each fiber. At positive r its record probabilities equal q_j. An empty fiber has no diagonal entries.

**Theorem 1.2 (Transfer of all three extrema to one state).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.physical_of_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.physical_of_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

At fixed original law q, an attained pinching gain B/r gives mutual information H(q) + B/r and conditional entropy −B/r on the same state. The same pointwise identities compare these quantities on every admissible state and give the opposite inequality for the conditional entropy.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.input_recordLaw`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets.physical_of_gain`
- Dependency: [D5/S3/Quantum/Measurement/Auric/EqualBlockProjection](EqualBlockProjection.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/ProjectiveRecord](ProjectiveRecord.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects](UnequalBlockEffects.md)
