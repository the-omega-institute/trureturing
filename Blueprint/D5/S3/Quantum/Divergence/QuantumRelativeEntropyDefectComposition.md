# Quantum Relative-Entropy Defect Composition

## Abstract

Quantum relative-entropy loss telescopes along composable matrix channels.

**Theorem 1.1 (Quantum relative-entropy defects form an additive channel chain).**

$$\forall a, b, c: \operatorname{Type},\ [\operatorname{Fintype}(a)], [\operatorname{DecidableEq}(a)],\ [\operatorname{Fintype}(b)], [\operatorname{DecidableEq}(b)],\ [\operatorname{Fintype}(c)], [\operatorname{DecidableEq}(c)],\ \phi: \operatorname{QuantumChannel}(a, b), \psi: \operatorname{QuantumChannel}(b, c),\ \rho, \sigma: \operatorname{DensityState}(a),\ \operatorname{relativeEntropyDefect}(\operatorname{comp}(\psi, \phi), \rho, \sigma) = \operatorname{relativeEntropyDefect}(\phi, \rho, \sigma) + \operatorname{relativeEntropyDefect}(\psi, \operatorname{mapState}(\phi, \rho), \operatorname{mapState}(\phi, \sigma)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.relative_entropy_defect_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The states are positive finite complex matrices of trace one. The channels are completely positive complex-linear maps that preserve the trace, and composition is constructed in that channel class.

Relative entropy is the real trace expression Re Tr(rho (log rho - log sigma)), using the pinned continuous-functional-calculus matrix logarithm. The defect is its value before the channel minus its value after the channel.

Expanding the three defects cancels the intermediate matrix-state relative entropy and gives the displayed identity.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.relative_entropy_defect_composition`
- Dependency: [D5/S3/Quantum/ChannelFixedState](../ChannelFixedState.md)
