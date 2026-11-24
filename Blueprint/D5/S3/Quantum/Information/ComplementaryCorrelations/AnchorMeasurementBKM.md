# Dual BKM estimate for measurement scores

## Abstract

Dual BKM estimate for measurement scores.

**Theorem 1.1 (Simpson bound for the inverse BKM form).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.omega_le_simpson`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.omega_le_simpson` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In an eigenbasis of the faithful state, each pair of eigenvalues contributes a logarithmic mean. The Simpson bound controls that mean by the arithmetic and geometric mean contributions.

**Theorem 1.2 (Dual estimate implies anchor convexity).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.anchorQuadraticIn_nonneg_of_simpson`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.anchorQuadraticIn_nonneg_of_simpson` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Center the two local score functions in each measured distribution. The marginal-free condition identifies their trace pairings with the measured Fisher forms. Weighted Cauchy–Schwarz then reduces nonnegativity to a Simpson bound on the joint centered observable.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.anchorQuadraticIn_nonneg_of_simpson`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementBKM.omega_le_simpson`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](../../Divergence/UmegakiRareFlagBKM.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../../Dynamics/ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement](AnchorMeasurement.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchorLogMean](CovarianceToAnchorLogMean.md)
- Dependency: [D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree](../RenyiInformationCombiningOrderThree.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMActualMetricCoordinates](../../Recovery/BKMActualMetricCoordinates.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMSpectralVariance](../../Recovery/BKMSpectralVariance.md)
