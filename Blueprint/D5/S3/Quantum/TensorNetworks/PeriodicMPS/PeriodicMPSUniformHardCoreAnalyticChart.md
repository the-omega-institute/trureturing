# The analytic fold in the actual hard-core chart

## Abstract

The analytic fold in the actual hard-core chart

**Theorem 1.1 (A fold after straightening the regular readouts).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart.exists_coherence_fold`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart.exists_coherence_fold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each length n ≥ 7 the seven regular normalized readouts, augmented by the imaginary part of the first coordinate, are analytic local coordinates at the witness. In these coordinates the negative real 00,01 coherence has a strict fold in the free variable.

**Theorem 1.2 (Transfer of chart recovery to actual projectors).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart.exists_generic_actual_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart.exists_generic_actual_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume there are chart points arbitrarily near the witness with equal regular observations and coherence and distinct forbidden-corner populations. The analytic fold theorem gives an open dense singleton-fiber locus in a chart neighborhood. Localization by the normalized marginal confines all actual competitors to a smaller compact chart set. Its compact image of the excluded set is closed, yielding a relatively open dense target set in an open neighborhood of the witness in the actual projector image.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart.exists_coherence_fold`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart.exists_generic_actual_reconstruction`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticFold](PeriodicMPSAnalyticFold.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFoldCurvature](PeriodicMPSUniformHardCoreFoldCurvature.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization](PeriodicMPSUniformHardCoreLocalization.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformZeroCorner](PeriodicMPSUniformZeroCorner.md)
