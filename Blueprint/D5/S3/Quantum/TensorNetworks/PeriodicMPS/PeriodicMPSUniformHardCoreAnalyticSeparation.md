# Quartic separation of actual hard-core paths

## Abstract

Quartic separation of actual hard-core paths

**Theorem 1.1 (The quartic survives passage to analytic paths).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation.forbidden_expansion_of_matched_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation.forbidden_expansion_of_matched_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each ring length n ≥ 7, assume the opposite-slope path matches the regular readouts and coherence exactly and has the stated cubic approximation by a polynomial chart path plus a cubic multiple of the null direction. The difference of the normalized 11,11 populations then has leading term quartic(n) times the fourth power of the path parameter. The transfer uses the vanishing first derivative and the null-line behavior of the forbidden corner to account for the cubic correction.

**Theorem 1.2 (Matched Taylor data imply actual reconstruction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation.exists_generic_actual_reconstruction_of_matched_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation.exists_generic_actual_reconstruction_of_matched_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parity Taylor data and exact matching give separated pairs arbitrarily close to the witness because quartic(n) is nonzero. The analytic chart theorem then gives generic targets in an actual-projector neighborhood, with every actual projector of the same length admitted as a competitor.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation.exists_generic_actual_reconstruction_of_matched_taylor`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation.forbidden_expansion_of_matched_taylor`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart](PeriodicMPSUniformHardCoreAnalyticChart.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetGerm](PeriodicMPSUniformHardCoreJetGerm.md)
