# Actual Cayley Residual Differential

## Abstract

The actual signed-Cayley measurement residual has an explicit directional derivative and a balanced scalar enclosure.

**Theorem 1.1 (The displayed residual derivative is derived from the actual matrix).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyHadamardDifferential.signed_cayley_hadamard_residual_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyHadamardDifferential.signed_cayley_hadamard_residual_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complex six-by-six matrix, the source differentiates the real and imaginary signed-Cayley coordinates along an affine real segment. Finite complex matrix multiplication and the squared-modulus product rule give the displayed scalar directional derivative. No supplied Jacobian correctness assumption is used. The five-coordinate dephased chart is obtained by fixing the first coordinate. This theorem does not itself certify interval arithmetic or a full Frechet-derivative implementation.

**Theorem 1.2 (The derived directional derivative yields a balanced row enclosure).**

Lean statement: `D5/S3/Quantum/Tomography/CayleyHadamardDifferential.signed_cayley_balanced_sublevel_row_enclosure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/CayleyHadamardDifferential.signed_cayley_balanced_sublevel_row_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source reuses HadamardResidualConservation for the six-outcome residual dual and Mathlib's scalar mean-value inequality on the complete closed segment. The actual residual derivative is the preceding theorem, not an input oracle. Numerical bounds on that formula, the seed Gram identity and the endpoint residual intervals remain explicit. The complete derivative remainder and the small-residual term are both retained. A successful external trace does not supply these Lean proof inputs.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/CayleyHadamardDifferential.signed_cayley_balanced_sublevel_row_enclosure`
- Truth anchor: `D5/S3/Quantum/Tomography/CayleyHadamardDifferential.signed_cayley_hadamard_residual_hasDerivAt`
- Dependency: [D5/S3/Quantum/Tomography/HadamardResidualConservation](HadamardResidualConservation.md)
