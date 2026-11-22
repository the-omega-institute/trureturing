# Quantum grading of the four-braid resolution cube

## Abstract

Quantum grading of the four-braid resolution cube

**Theorem 1.1 (Bounds from all smoothing choices).**

Lean statement: `D5/S3/Topology/FourBraidKhovanovResolutions.upperQuantum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FourBraidKhovanovResolutions.upperQuantum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed braid contains eleven signed crossings. Each smoothing choice selects one matching at each crossing and closes the last slice onto the first. The normalized quantum degree of the all-one label on any smoothing is odd and at most 21. The verified finite computation uses the actual circles from the matching graph. Changing a circle label to X decreases the quantum degree by two.

**Theorem 1.2 (Higher and even quantum gradings have empty bases).**

Lean statement: `D5/S3/Topology/FourBraidKhovanovResolutions.basis_empty_of_above_or_even`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FourBraidKhovanovResolutions.basis_empty_of_above_or_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every cohomological degree has an empty basis in any even quantum grading and in every quantum grading above 21. Thus the comparison with the first nonzero row starting at the diagram's potential top needs only the odd gradings 21, 19 and 17.

## References

- Truth anchor: `D5/S3/Topology/FourBraidKhovanovResolutions.basis_empty_of_above_or_even`
- Truth anchor: `D5/S3/Topology/FourBraidKhovanovResolutions.upperQuantum_bound`
- Dependency: [D5/S3/Topology/FourBraidKhovanovResolutionData](FourBraidKhovanovResolutionData.md)
