# Adaptive Separation Depth Upper Bound

## Abstract

Pair-separating readouts on a finite state quotient construct an identifying adaptive protocol tree with worst realized depth at most one less than the number of states.

**Theorem 1.1 (Pair separation gives a state-count adaptive depth bound).**

$$\begin{aligned}\forall C, P, A: \operatorname{Type},\\{}[\operatorname{Fintype}(C)],\\\forall q: P \to C \to A,\\{}(\forall x, y: C, x \neq y \Rightarrow \exists p: P, q(p, x) \neq q(p, y)) \Rightarrow\\\exists T: \operatorname{PassiveProtocol}(P, {(_: P) \mapsto A}), \operatorname{Injective}(\operatorname{runPassiveProtocol}(q, T)) \land\\{}\forall x: C, \operatorname{length}(\operatorname{runPassiveProtocol}(q, T)(x)) \leq \operatorname{card}(C) - 1.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound.adaptive_separation_depth_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction on the current finite candidate set chooses a readout separating two candidates. Every realized answer fiber is a strict subset, so recursion identifies that branch within one fewer query than the current candidate count.

## References

- Truth anchor: `D5/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound.adaptive_separation_depth_upper_bound`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../../ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.md)
