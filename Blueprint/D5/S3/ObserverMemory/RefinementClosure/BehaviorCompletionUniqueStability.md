# Behavior Completion Unique Stability

## Abstract

The completed behavior range has a unique induced source update.

**Theorem 1.1 (The induced update on completed behavior is unique).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}F: X \to X, q: X \to B,\\{}\exists! induced: \operatorname{ItineraryRange}(F, q) \to \operatorname{ItineraryRange}(F, q),\\{}\operatorname{rangeFactorization}(\operatorname{completeItinerary}(F, q)) \circ F = induced \circ \operatorname{rangeFactorization}(\operatorname{completeItinerary}(F, q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionUniqueStability.behavior_completion_has_unique_induced_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update a state type X and let q read states into B. No surjectivity assumption is imposed on q.

The completion carrier is the realized range of the full future q-itinerary, and the public interface is Mathlib's canonical factorization through that range.

The existing itinerary update supplies an induced map making the displayed square commute. Surjectivity of the canonical range factorization cancels its right composition and proves that every other commuting induced map is equal to it.

Repository searches found no exact public exists-unique theorem. The proof reuses the canonical completion objects and directly applies the pinned range-factorization surjectivity theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionUniqueStability.behavior_completion_has_unique_induced_update`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
