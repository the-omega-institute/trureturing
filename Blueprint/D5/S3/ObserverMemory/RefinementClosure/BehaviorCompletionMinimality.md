# Behavior Completion Minimality

## Abstract

Behavior completion is the least stable refinement of a readout interface.

**Theorem 1.1 (Behavior completion is the least stable refinement).**

$$\begin{gathered}\forall X, B, R: \operatorname{Type},\\F: X \to X, q: X \to B, r: X \to R,\\\operatorname{Surjective}(q) \land \operatorname{Surjective}(r) \land\\(\exists G: R \to R, r \circ F = G \circ r) \land\\(\exists! \pi: R \to B, q = \pi \circ r) \Rightarrow\\\exists! Phi: R \to \operatorname{ItineraryRange}(F, q), \operatorname{rangeFactorization}(\operatorname{completeItinerary}(F, q)) = Phi \circ r.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionMinimality.behavior_completion_is_least_stable_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update source states. Let q and r be surjective interfaces onto their effective images. Stability of r is exposed by an induced update, and refinement of q through r is exposed by its unique readout factor.

The behavior completion is the realized range of the full future q-word. The theorem constructs a unique map from the effective codomain of r to that realized completion range whose composition with r is the canonical completion projection.

Prediction completion universality first supplies a word-valued factor. Surjectivity of r shows every such word is realized by a source state, yielding the effective-range factor, and also cancels r to prove uniqueness.

The frozen repository universality theorem is applied directly. It is not an exact bind because it omits the effective-image codomain and unique factor required here. Pinned Mathlib supplies range factorization and surjective composition cancellation.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionMinimality.behavior_completion_is_least_stable_refinement`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality](../PredictionFactors/PredictionCompletionUniversality.md)
