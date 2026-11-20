# Localization from the hard-core marginal

## Abstract

Localization from the hard-core marginal

**Theorem 1.1 (The complete compact witness fiber).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization.closure_actualProjectors_witness_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization.closure_actualProjectors_witness_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n ≥ 7 the trace-one witness projector is the only point in the compact closure of the actual projector image with its adjacent two-site marginal. A point in the closure is a rank-one projector with cyclic columns. The fixed-witness recovery result for cyclic amplitudes then identifies its ray.

**Theorem 1.2 (Control of every actual competitor near the witness observation).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization.exists_open_normalizedMarginal_localization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization.exists_open_normalizedMarginal_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compactness and continuity keep every projector above a sufficiently small open marginal neighborhood near the witness projector. The vacuum coordinate gives a continuous full-amplitude representative there. Applying the ordinary decoder to that representative forces the first core trace to be nonzero and places the ordinary trace invariants in any prescribed neighborhood of the witness invariants.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization.closure_actualProjectors_witness_fiber`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization.exists_open_normalizedMarginal_localization`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCorePencilDecoder](PeriodicMPSUniformHardCorePencilDecoder.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSCompactFiber](../PeriodicMPSCompactFiber.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSProjectiveCoordinates](../PeriodicMPSProjectiveCoordinates.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness](../PeriodicMPSUniformHardCoreMarginalWitness.md)
