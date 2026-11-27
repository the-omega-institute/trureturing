# Relative entropy sensitivity for a prescribed measurement

## Abstract

An exact four-term sensitivity loss for a prescribed finite POVM.

**Theorem 1.1 (Four contributions to the loss).**

Lean statement: `D5/S3/Quantum/Information/PovmSensitivityDefect.sensitivity_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PovmSensitivityDefect.sensitivity_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lucas Chibebe Céleri and Diogo de Oliveira Soares-Pinto (2026). *Rugosity as a measurement-induced relative entropy*. URL: <https://arxiv.org/abs/2611.34788v1>.

*Commentary.*

At a full-rank state with positive outcome masses, weight the POVM effects by their Born probability derivatives divided by their masses. The loss from the BKM cost to the scalar sensitivity splits into a squared BKM distance, a logarithmic-mean gap, a sum of positive POVM sandwiches, and the squared residual of the classical score projection. The logarithmic-mean gap controls one third of the squared Frobenius norm of the commutator with the square root of the state.

**Theorem 1.2 (Sensitivity for reverse relative entropy).**

Lean statement: `D5/S3/Quantum/Information/PovmSensitivityDefect.reverseKL_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PovmSensitivityDefect.reverseKL_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lucas Chibebe Céleri and Diogo de Oliveira Soares-Pinto (2026). *Rugosity as a measurement-induced relative entropy*. URL: <https://arxiv.org/abs/2611.34788v1>.

*Commentary.*

Use the centered score one minus the reference mass divided by the Born mass. The score pairing gives the directional derivative of reverse relative entropy. Its squared norm is Pearson chi-squared divergence. A point-mass reference includes the flat-state outcome of the binary rugosity measurement.

**Theorem 1.3 (Sensitivity for forward relative entropy).**

Lean statement: `D5/S3/Quantum/Information/PovmSensitivityDefect.forwardKL_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PovmSensitivityDefect.forwardKL_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lucas Chibebe Céleri and Diogo de Oliveira Soares-Pinto (2026). *Rugosity as a measurement-induced relative entropy*. URL: <https://arxiv.org/abs/2611.34788v1>.

*Commentary.*

Use the log ratio of Born and reference masses centered by relative entropy. With a positive reference distribution its squared norm is the relative entropy variance. The same four terms account for the loss along the affine Born curve.

## References

- Truth anchor: `D5/S3/Quantum/Information/PovmSensitivityDefect.forwardKL_decomposition`
- Truth anchor: `D5/S3/Quantum/Information/PovmSensitivityDefect.reverseKL_decomposition`
- Truth anchor: `D5/S3/Quantum/Information/PovmSensitivityDefect.sensitivity_decomposition`
- Dependency: [D5/S3/Divergence/ClassicalDPI](../../Divergence/ClassicalDPI.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM](ComplementaryCorrelations/AnchorMeasurementBKM.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/LiuWildProductProbes](../ProcessReconstruction/LiuWildProductProbes.md)
