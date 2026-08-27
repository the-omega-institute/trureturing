# Observer Pullback Trace Identity

## Abstract

Iterated channel evolution and Heisenberg pullback have equal trace readouts.

**Theorem 1.1 (Channel iterates equal iterated effect pullbacks).**

$$\begin{gathered}\forall d: \operatorname{Type}, \operatorname{Fintype}(d), \operatorname{DecidableEq}(d),\\{}\phi: \operatorname{QuantumChannel}(d, d), \phi^{*}: \operatorname{CompletelyPositiveMap}(\operatorname{Matrix}(d, d, \mathbb{C}), \operatorname{Matrix}(d, d, \mathbb{C})),\\{}(\forall X, A: \operatorname{Matrix}(d, d, \mathbb{C}), \operatorname{Tr}(\phi(X) A) = \operatorname{Tr}(X \phi^{*}(A))),\\{}t: \operatorname{Nat}, \rho: \operatorname{DensityState}(d), E: \operatorname{Matrix}(d, d, \mathbb{C}),\\{}\operatorname{Tr}((\phi)^{t}(\rho) E) = \operatorname{Tr}(\rho (\phi^{*})^{t}(E)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ObserverPullbackTraceIdentity.observer_pullback_trace_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite carrier is the existing complex matrix algebra. The Schrodinger map is an existing completely positive trace-preserving quantum channel, and rho is an existing positive trace-one density state.

The Heisenberg map is completely positive and is related to the channel by the displayed one-step trace-duality premise. The effect may be any matrix, so physical effects are included without an extra restriction.

Induction moves one channel use across the trace pairing at each step. The two canonical iterate recursion laws identify the resulting expression with the same number of Heisenberg pullbacks.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ObserverPullbackTraceIdentity.observer_pullback_trace_identity`
- Dependency: [D5/S3/Quantum/Fibers/FutureStatisticsEquivalence](../Fibers/FutureStatisticsEquivalence.md)
