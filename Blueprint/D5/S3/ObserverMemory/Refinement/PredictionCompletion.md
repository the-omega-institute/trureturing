# Predictive Completion under Observation Refinement

## Abstract

Observation refinement induces a unique surjective map of predictive completions.

**Theorem 1.1 (Refinement induces the canonical predictive quotient map).**

$$r = h \circ q \Rightarrow\ R_{q} \subseteq R_{r} \land\ \exists! kappa: Z_{q} \to Z_{r},\ \operatorname{Surjective}\left(kappa\right) \land\ \pi_{r} = kappa \circ \pi_{q} \land\ kappa \circ \overline{\tau}_{q} = \overline{\tau}_{r} \circ kappa \land\ \overline{r} \circ kappa = h \circ \overline{q}.$$

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
