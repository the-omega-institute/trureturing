# Complex Hadamard classification in dimensions two and three

## Abstract

Complex Hadamard classification in dimensions two and three.

**Theorem 1.1 (Qubit flat unitaries).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_two_equivalent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_two_equivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rescale the entry moduli to one and dephase the first row and column. Orthogonality determines the remaining entry.

**Theorem 1.2 (Qutrit flat unitaries).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_three_equivalent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_three_equivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A dephased row of length three orthogonal to the all-ones row has the two nontrivial cube roots of unity in its last entries. Orthogonality forces the two rows to use opposite orders.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_three_equivalent`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard.flat_two_equivalent`
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement](AnchorMeasurement.md)
- Dependency: [D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided](../../Tomography/MUB/ComplexHadamardTwoSided.md)
