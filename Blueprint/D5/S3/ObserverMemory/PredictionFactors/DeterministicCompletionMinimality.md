# Deterministic Completion Minimality

## Abstract

Finite deterministic realizations factor uniquely onto the completed state.

**Theorem 1.1 (Finite deterministic realizations factor uniquely through the completion).**

$$\begin{gathered}\forall Y: \operatorname{Type}, O: \operatorname{Type}, W: \operatorname{Type},\\{}[\operatorname{Finite}\left(Y\right)], [\operatorname{Finite}\left(W\right)],\\{}F: Y \to Y, q: Y \to O,\\{}r: Y \to W, G: W \to W, s: W \to O,\\{}(\operatorname{Surjective}\left(r\right) \land r \circ F = G \circ r \land q = s \circ r)\\{}\Rightarrow (\exists! h: W \to \operatorname{CompletedState}\left(F, q\right),\\{}\operatorname{Surjective}\left(h\right) \land \operatorname{completionProjection}\left(F, q\right) = h \circ r \land\\{}h \circ G = \operatorname{completionUpdate}\left(F, q\right) \circ h \land\\{}\operatorname{completionReadout}\left(F, q\right) \circ h = s) \land\\{}\operatorname{card}\left(\operatorname{CompletedState}\left(F, q\right)\right) \leq \operatorname{card}\left(W\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/DeterministicCompletionMinimality.minimal_deterministic_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update source states and q read them out. A finite implementation consists of a surjective state map r together with an update G and readout s for which both the update and readout squares commute.

The completed carrier is the repository's canonical quotient by equality of complete future readout itineraries. The theorem constructs the factor from representatives of r-fibers and proves that the full itinerary factorization makes this construction independent of the chosen representatives.

The resulting factor is uniquely determined, surjective, commutes with the canonical projection and update, and preserves the readout. Its surjectivity gives the displayed finite cardinal lower bound.

The proof directly applies the repository theorem prediction_completion_universality and the pinned-library declarations Function.surjInv, Function.rightInverse_surjInv, and Nat.card_le_card_of_surjective. Searches found no equal or stronger theorem carrying all five public clauses and uniqueness together.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/DeterministicCompletionMinimality.minimal_deterministic_completion`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality](PredictionCompletionUniversality.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](../Refinement/PredictionCompletion.md)
