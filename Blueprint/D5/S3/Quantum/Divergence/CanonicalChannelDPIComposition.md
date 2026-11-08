# Composite Quantum Channel Data Processing

## Abstract

Support-aware quantum relative entropy contracts along a composite finite channel.

**Theorem 1.1 (Data processing is closed under sequential composition).**

Lean statement: `D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition.extended_quantum_relative_entropy_comp_dpi`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition.extended_quantum_relative_entropy_comp_dpi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing support-aware data-processing theorem to the second channel on the intermediate state pair, then to the first channel on the original pair. QuantumChannel.comp_mapState identifies the composite action with sequential state evolution.

The three finite carriers may live in independent universes. Singular states remain covered by the existing WithTop-valued support-aware relative entropy.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition.extended_quantum_relative_entropy_comp_dpi`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalChannelDPI](CanonicalChannelDPI.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
