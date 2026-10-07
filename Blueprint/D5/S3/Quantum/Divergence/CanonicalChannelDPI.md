# Canonical Quantum Channel Data Processing

## Abstract

Support-aware quantum relative entropy decreases under every finite quantum channel.

**Theorem 1.1 (Data processing including singular noncommuting states).**

$$\forall u, v: \operatorname{Level},\ a: \operatorname{Type} u, b: \operatorname{Type} v,\ [\operatorname{Fintype}(a)], [\operatorname{DecidableEq}(a)], [\operatorname{Nonempty}(a)],\ [\operatorname{Fintype}(b)], [\operatorname{DecidableEq}(b)], [\operatorname{Nonempty}(b)],\ \phi: \operatorname{QuantumChannel}(a, b),\ \rho, \sigma: \operatorname{DensityState}(a),\ \operatorname{extendedQuantumRelativeEntropy}(\operatorname{mapState}(\phi, \rho), \operatorname{mapState}(\phi, \sigma)) \le \operatorname{extendedQuantumRelativeEntropy}(\rho, \sigma).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi` (`✓ std3`). ∎

*Citation.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

The input and output carriers are arbitrary finite decidable nonempty types in independent universes. DensityState is the actual positive semidefinite complex matrix of trace one. QuantumChannel is a bundled completely positive complex-linear trace-preserving map, and mapState is its action on that same state.

The entropy takes values in the real numbers with top adjoined. It equals Re Tr(rho (log rho - log sigma)) when ker(sigma) is contained in ker(rho), and top otherwise. The spectral logarithm uses natural logarithms and is totalized at zero. Singular states and noncommuting pairs remain in the theorem's scope.

One Kraus family gives support transfer and both Schwarz inequalities. The positive-support eigenfamilies give exact trace-log coordinates and a contraction V satisfying V eta = xi, V* V <= I, and V* A V <= B. The square-root defect extends V to an isometry and annihilates eta.

Reflection across the isometry range and finite eigenvector intertwining give logarithm compression. Operator logarithm monotonicity applies to strictly positive regularized matrices. A finite scalar logarithm limit then proves the supported inequality; the unsupported input has top on the right. This is the finite matrix form of the established Petz and Hiai-Mosonyi-Petz-Beny support contraction argument.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi`
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
