# Finite dynamic residual composition

## Abstract

Dynamic errors of finite quantum channels compose with a rescaled second time window.

**Definition 1.1 (Finite-window stabilized discrepancy).**

Lean statement: `D5/S3/Quantum/Dynamics/FiniteDynamicResidualComposition.dynamicResidual`

*Formalization.* `D5/S3/Quantum/Dynamics/FiniteDynamicResidualComposition.dynamicResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a canonical finite CPTP channel C from A to B and specified real-time CPTP families PA and PB, dynamicResidual C PA PB a T is one half of the real supremum of diamondDistance (C comp PA(t)) (PB(a t) comp C) over 0 <= t <= T. diamondDistance is the existing unhalved distance tested on joint density states with every finite reference dimension. Its values lie in [0,2]. A zero element is included in the supremum set to define empty windows. For T >= 0, the window contains t = 0, and all distances are nonnegative, so this extra element does not change the time supremum. The residual therefore lies in [0,1].

**Theorem 1.2 (Composition with the rescaled horizon).**

Lean statement: `D5/S3/Quantum/Dynamics/FiniteDynamicResidualComposition.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FiniteDynamicResidualComposition.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A, B and C be independent finite decidable coordinate types, C1 a CPTP channel from A to B, and C2 a CPTP channel from B to C. For arbitrary specified CPTP families PA, PB and PC, positive real a and b, and T >= 0, the residual of C2 comp C1 at scale a*b and horizon T is at most the residual of C1 at scale a and horizon T plus the residual of C2 at scale b and horizon a*T.

At each time insert C2 comp PB(a*t) comp C1 between the two composite-channel outputs. Rectangular CPTP trace-distance contraction applies after every finite reference amplification to bound the first error. The second error is tested on the joint state obtained by applying C1 to the original input. The triangle inequality and the two stabilized suprema give the pointwise sum. Since 0 <= a*t <= a*T and b*(a*t) = (a*b)*t, the time supremum gives the asserted bound. The sole factor one half is applied after the unhalved estimates. Bounded nonempty real suprema suffice; no maximum is asserted. T = 0 is included, without asserting that the families are identity channels at zero.

The entropy balance is a separate application of QuantumRelativeEntropyDefectComposition.relative_entropy_defect_composition. Convert canonical channels and states with LegacyRelativeEntropyBoundary; its legacy_quantumRelativeEntropy_eq_finite_branch identifies the trace-log scalar. When the input, intermediate and final state pairs have compatible supports, SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_coe_of_support identifies these scalars with the finite Umegaki values. The intermediate entropy cancels exactly. CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi makes both losses nonnegative. Subtraction of two infinite values is outside this finite balance.

These are channel composition properties. They impose no semigroup, continuity, differentiability, generator, recovery or spatial locality condition. The entropy identity does not specify effective dynamics, and a dynamic residual bound does not construct recovery of a selected state family. A renormalization interpretation requires additional scale, rescaling, coupling and locality data. Finite classical probability models use the corresponding commuting diagonal states; a separate stochastic-to-CPTP realization must be supplied when applying that specialization.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteDynamicResidualComposition.dynamicResidual`
- Truth anchor: `D5/S3/Quantum/Dynamics/FiniteDynamicResidualComposition.result`
- Dependency: [D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance](../../QuantumChannels/SchurChannelMixedUnitaryDistance.md)
