# Hadamard Residual Conservation

## Abstract

Actual six-outcome residual conservation sharpens validated MUB sublevel enclosures.

**Theorem 1.1 (Balanced endpoint dual for the actual matrix residual).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.hadamard_residual_box_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.hadamard_residual_box_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H H*=6I and six unit-modulus input coordinates, the six squared-modulus residuals sum to zero. Subtracting any common dual coefficient from the readout row preserves its value. Endpoint products then give lower and upper bounds on every real residual in the given intervals. The matrix conservation law is derived in the proof; rational residuals, a numerical root, and dual optimality are not assumed.

**Theorem 1.2 (Asymmetric conserved-residual Newton-row enclosure).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.balanced_hadamard_sublevel_row_enclosure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.balanced_hadamard_sublevel_row_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit Hadamard residual and its actual Frechet derivative feed the existing SublevelRowEnclosure owner. Applying that theorem to f-f(x) isolates the full directional remainder; the balanced dual supplies the remaining endpoint interval. Interval-expression soundness and complete traversal reflection remain separate obligations. An external checker result is not a premise of this theorem.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.balanced_hadamard_sublevel_row_enclosure`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/HadamardResidualConservation.hadamard_residual_box_dual`
- Dependency: [D5/S3/Quantum/Tomography/HadamardResidualBarrier](../HadamardResidualBarrier.md)
- Dependency: [D5/S3/Quantum/Tomography/SublevelRowEnclosure](../SublevelRowEnclosure.md)
