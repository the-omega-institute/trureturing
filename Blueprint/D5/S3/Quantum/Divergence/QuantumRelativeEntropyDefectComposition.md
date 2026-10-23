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

For canonical finite CPTP channels C1:A->B and C2:B->C, use LegacyRelativeEntropyBoundary to convert the same channels and the same input pair rho,sigma to the legacy structures. Its adapters preserve matrix action, channel composition and the intermediate pair C1(rho),C1(sigma). legacy_quantumRelativeEntropy_eq_finite_branch identifies the scalar with the canonical finite trace-log branch. When SupportContained holds for the input, intermediate and final pairs, SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_coe_of_support identifies each scalar with its finite Umegaki relative entropy. The existing telescope therefore gives ell_(C2 comp C1)(rho,sigma) = ell_C1(rho,sigma) + ell_C2(C1(rho),C1(sigma)), where each ell is the input relative entropy minus its channel-output relative entropy. CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi, applied to C1 on the input pair and C2 on that same intermediate pair, makes both losses nonnegative. Density trace one supplies any needed Nonempty instance. All three relative entropies are finite; this argument makes no subtraction of infinite values. A complete classical specialization still requires an actual arbitrary finite rectangular stochastic-channel realization as canonical CPTP maps and the diagonal KL identification, including its zero and support conventions. Those bridges are not proved here. This entropy balance specifies no effective dynamics; its right side cannot replace a dynamic residual estimate.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.relative_entropy_defect_composition`
- Dependency: [D5/S3/Quantum/ChannelFixedState](../ChannelFixedState.md)
