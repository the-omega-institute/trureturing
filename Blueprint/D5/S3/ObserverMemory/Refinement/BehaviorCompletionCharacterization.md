# Behavior Completion Characterization

## Abstract

Universal stable completion is uniquely equivalent to canonical completion.

**Theorem 1.1 (The universal stable completion is canonical).**

$$\forall W, u, r, c, U, R,\ (\operatorname{Surjective}(c) \land\ c \circ u = U \circ c \land\ r = R \circ c) \land\ (\forall V, v, S, s,\ (\operatorname{Surjective}(v) \land\ v \circ u = S \circ v \land\ r = s \circ v) \Rightarrow \exists! f: V \to W, c = f \circ v) \Rightarrow\ \exists! e: \operatorname{Equiv}(W, \operatorname{Completion}(u, r)), \operatorname{Projection}(u, r) = e \circ c.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/BehaviorCompletionCharacterization.behavior_completion_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let candidate be an effective interface for the source state: it is surjective, its update is stable under the source update, and its readout preserves the original readout. Assume further that every effective stable refinement factors uniquely through candidate.

The canonical completed-state projection is itself an effective stable refinement preserving the readout, so universality supplies the map back to candidate. A surjective choice of representatives supplies the forward map. Their projection equations make them inverse, and surjectivity proves uniqueness of the resulting equivalence.

The canonical completion declarations and the existing prediction universality theorem are imported from the ObserverMemory family. The finite minimality theorem is not an exact hit. Repository and pinned-Mathlib searches found no theorem combining all premises with the unique canonical equivalence.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/BehaviorCompletionCharacterization.behavior_completion_characterization`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality](../PredictionFactors/PredictionCompletionUniversality.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](PredictionCompletion.md)
