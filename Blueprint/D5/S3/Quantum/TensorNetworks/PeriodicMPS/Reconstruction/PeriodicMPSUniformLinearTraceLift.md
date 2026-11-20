# Weighted trace coordinates from periodic amplitudes

## Abstract

Weighted trace coordinates from periodic amplitudes

**Theorem 1.1 (Uniform linear trace-word readout).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift.linearReadout_traceWord`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift.linearReadout_traceWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adam Czapliński; Mateusz Michałek; Tim Seynnaeve (2023). *Uniform matrix product states from an algebraic geometer's point of view*. DOI: [10.1016/j.aam.2022.102417](https://doi.org/10.1016/j.aam.2022.102417). URL: <https://arxiv.org/abs/1904.07563v1>.

*Commentary.*

At length six plus r, six fixed signed contrasts of complete binary amplitudes recover the weighted invariant vector times twice the negative commutator determinant and the trace of the r-th power of the first core. The six degree-six word combinations evaluate to scalar matrices before the extra letters are appended.

**Theorem 1.2 (Unique lift on the compact graph).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift.lift_eq_of_readColumn_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift.lift_eq_of_readColumn_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adam Czapliński; Mateusz Michałek; Tim Seynnaeve (2023). *Uniform matrix product states from an algebraic geometer's point of view*. DOI: [10.1016/j.aam.2022.102417](https://doi.org/10.1016/j.aam.2022.102417). URL: <https://arxiv.org/abs/1904.07563v1>.

*Commentary.*

If the first contrast of a full-projector column is nonzero, the projector of the contrast vector determines the weighted trace projector throughout the compact graph. The condition holds at the independent-set witness for each length.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift.lift_eq_of_readColumn_ne_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift.linearReadout_traceWord`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSProjectiveCoordinates](../../PeriodicMPSProjectiveCoordinates.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil](../../PeriodicMPSUniformDeterminantPencil.md)
