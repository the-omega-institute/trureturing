# Hadamard Squared Minor Separation

## Abstract

Squared minors obstruct equivalence to a matrix with a squared row or column pair.

**Theorem 1.1 (Squared minor obstruction).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/HadamardSquaredMinorSeparation.not_hadamardEquivalent_of_squared_minor_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/HadamardSquaredMinorSeparation.not_hadamardEquivalent_of_squared_minor_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex square matrices H and K on any coordinate type, suppose every distinct row pair and every distinct column pair of the entrywise square of H has a nonzero two-by-two minor. If K has a distinct row or column pair whose squared minors all vanish, then H and K are not Hadamard equivalent.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/HadamardSquaredMinorSeparation.not_hadamardEquivalent_of_squared_minor_separation`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility](MUBHadamardCompatibility.md)
