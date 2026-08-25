# Stochastic Target Completion

## Abstract

Conditional-law completion is the least prediction-sufficient conservative refinement.

**Theorem 1.1 (Conditional-law completion is the least sufficient refinement).**

$$\begin{gathered}\forall X, C, Y: \operatorname{Type},\\{}[\operatorname{Fintype}(X)],\\{}concept: X \to C, K: X \to \operatorname{PMF}\left(Y\right),\\{}\operatorname{TargetSufficient}\left(\operatorname{targetClosure}\left(concept, K\right), K\right) \land\\{}\operatorname{Refines}\left(concept, \operatorname{targetClosure}\left(concept, K\right)\right) \land\\{}\forall D: \operatorname{Type}, candidate: X \to D,\\{}\operatorname{Refines}\left(concept, candidate\right) \Rightarrow \operatorname{TargetSufficient}\left(candidate, K\right) \Rightarrow \operatorname{Refines}\left(\operatorname{targetClosure}\left(concept, K\right), candidate\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/StochasticTargetCompletion.stochastic_target_completion_is_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite source state is assigned its complete conditional law in PMF(Y). Completing a concept joins its original readout with that law-valued kernel.

The completed concept is prediction-sufficient and still refines the original concept. Thus it preserves the old information while making the full conditional distribution recoverable.

Every other concept that both refines the original readout and makes the same kernel recoverable also receives a factor map from the completion. This is the claimed least conservative completion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/StochasticTargetCompletion.stochastic_target_completion_is_least`
- Dependency: [D5/S3/ConceptDynamics/Completion/TargetClosureReflection](TargetClosureReflection.md)
