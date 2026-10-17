# Compact Observation Subshifts

## Abstract

Compact continuous finite observations form closed shift-invariant sofic languages.

**Definition 1.1 (Observation language).**

$$\begin{aligned}\forall X: Type u, A: Type v, f: X \Rightarrow X, a: X \Rightarrow A,\\observationLanguage(f, a) = Set.range(x \mapsto (n \mapsto a(Function.iterate(f, n, x)))).\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.observationLanguage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation language is the range of x↦(n↦a(f^[n](x))).

**Theorem 1.2 (Continuous observation names).**

$$\begin{aligned}\forall X: Type u, [TopologicalSpace(X)], A: Type v, [TopologicalSpace(A)],\\f: X \Rightarrow X, a: X \Rightarrow A, Continuous(f) \land Continuous(a) \Rightarrow Continuous(x\mapsto(n \mapsto a(Function.iterate(f, n, x)))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.continuous_observationName` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity of the dynamics and readout gives continuity into the countable product.

**Theorem 1.3 (Compact and closed observation language).**

$$\begin{aligned}\forall X: Type u, [TopologicalSpace(X)], [CompactSpace(X)], A: Type v, [TopologicalSpace(A)], [DiscreteTopology(A)], [Finite(A)],\\f: X \Rightarrow X, a: X \Rightarrow A, Continuous(f) \land Continuous(a) \Rightarrow IsCompact(observationLanguage(f, a)) \land IsClosed(observationLanguage(f, a)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.observationLanguage_isCompact_isClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compact source and finite discrete alphabet make the observation range compact and closed.

**Theorem 1.4 (Shift invariance).**

$$\begin{aligned}\forall f: X \Rightarrow X, a: X \Rightarrow A, w: \mathbb{N} \Rightarrow A, w \in observationLanguage(f, a) \Rightarrow (n \mapsto w(n+1)) \in observationLanguage(f, a).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.observationLanguage_shift_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Shifting a complete observation name is the name of the forward image point.

**Theorem 1.5 (Compact observation subshift is closed, invariant and sofic).**

$$\begin{aligned}\forall X: Type u, [TopologicalSpace(X)], [CompactSpace(X)], A: Type v, [TopologicalSpace(A)], [DiscreteTopology(A)], [Finite(A)],\\f: X \Rightarrow X, a: X \Rightarrow A, Continuous(f) \land Continuous(a) \Rightarrow HasShadowing(f) \Rightarrow IsSofic(observationLanguage(f, a)) \land IsClosed(observationLanguage(f, a)) \land \forall w: \mathbb{N} \Rightarrow A, w \in observationLanguage(f, a) \Rightarrow (n \mapsto w(n+1)) \in observationLanguage(f, a).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.compact_observation_is_closed_shift_invariant_sofic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

For a compact source with continuous dynamics and a continuous finite discrete readout, the observed language is compact and closed. Under HasShadowing, the finite-observation graph construction gives an exact sofic presentation, and the forward shift preserves the range. This is a formal bridge from topological dynamics to symbolic dynamics; it does not resolve the global zero-dimensional extension questions.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.compact_observation_is_closed_shift_invariant_sofic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.continuous_observationName`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.observationLanguage`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.observationLanguage_isCompact_isClosed`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactObservationSubshift.observationLanguage_shift_invariant`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteObservationSofic](FiniteObservationSofic.md)
