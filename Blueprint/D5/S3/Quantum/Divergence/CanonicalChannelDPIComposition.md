# Composite Quantum Channel Data Processing

## Abstract

Support-aware quantum relative entropy contracts along a finite sequential channel.

**Theorem 1.1 (Composite-channel data processing).**

Lean statement: `D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition.extended_quantum_relative_entropy_comp_dpi`.

*Proof.* Apply the existing canonical data-processing theorem to the second channel on the intermediate state pair, then to the first channel on the original pair. `QuantumChannel.comp_mapState` identifies the composite action with this sequential action. ∎

The result is a categorical closure property of the support-aware finite Umegaki relative entropy. It introduces no additional support or faithfulness assumptions beyond those already required by the one-step theorem, and it permits three independent finite carriers.

**Dependencies.**

- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi`
- Composition law: `D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.comp_mapState`
- Source module: `D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition`
