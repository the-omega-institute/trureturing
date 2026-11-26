# Rank-one products around a cycle

## Abstract

The independent-set indicator as a rank-one-core trace tensor

**Theorem 1.1 (Cyclic product of adjacent dot products).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_rankOne`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty word and outer-product cores uₐvₐᵀ, the trace amplitude is the product of vₐᵀuᵦ over ordered adjacent symbols around the cycle. Multiplying the rank-one factors produces the dot products along the word, and the trace supplies the last-to-first dot product.

**Theorem 1.2 (Literal independent-set amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_witnessCore_eq_indicator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_witnessCore_eq_indicator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the two explicit witness cores the adjacent dot product is zero on 11 and one on 00, 01 and 10. Thus at each length n ≥ 7 the trace amplitude is exactly one on words whose occupied sites are independent in the cycle, and zero on every other word. The trace enforces the exclusion across the seam.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_rankOne`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_witnessCore_eq_indicator`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil](PeriodicMPSUniformDeterminantPencil.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts](PeriodicMPSUniformHardCoreCounts.md)
