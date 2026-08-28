# Predictive Completion under Observation Refinement

## Abstract

Observation refinement induces a unique surjective map of predictive completions.

**Theorem 1.1 (Refinement induces the canonical predictive quotient map).**

$$\forall Y \in \operatorname{Type}, O \in \operatorname{Type}, P \in \operatorname{Type}, update \in Y \to Y, fine \in Y \to O, coarse \in Y \to P, forget \in O \to P, hfactor \in coarse = forget \circ fine,\; \operatorname{ker}(\operatorname{completeItinerary}(update, fine)) \subseteq \operatorname{ker}(\operatorname{completeItinerary}(update, coarse)) \land \exists! descend: \operatorname{Function}(\operatorname{CompletedState}(update, fine), \operatorname{CompletedState}(update, coarse)), \operatorname{Surjective}(descend) \land \left(\operatorname{completionProjection}(update, coarse) = descend \circ \operatorname{completionProjection}(update, fine) \land \left(descend \circ \operatorname{completionUpdate}(update, fine) = \operatorname{completionUpdate}(update, coarse) \circ descend \land \operatorname{completionReadout}(update, coarse) \circ descend = forget \circ \operatorname{completionReadout}(update, fine)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/PredictionCompletion.observation_refinement_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the coarse readout is obtained by applying forget to the fine readout. Applying forget at every time sends equality of complete fine itineraries to equality of complete coarse itineraries.

The repository theorem relative_identity_refinement then gives the unique surjection between the two kernel quotients and its projection factorization. Quotient induction verifies that the same map intertwines the induced update and current readout.

Pinned Mathlib supplies Setoid.map_of_le, Setoid.lift_unique, Quotient.map, and Quotient.lift through the imported repository modules. Loogle and third-party searches found no declaration combining the relation, uniqueness, surjectivity, and both intertwining equations.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/PredictionCompletion.observation_refinement_completion`
- Dependency: [D5/S0/Rewriting/Quotients/RelativeIdentityRefinement](../../../S0/Rewriting/Quotients/RelativeIdentityRefinement.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
