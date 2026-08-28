# Cascade Completion

## Abstract

Fine completion followed by coarse completion is direct coarse completion.

**Theorem 1.1 (The completion cascade identifies with direct coarse completion).**

$$\forall tau, q, r, h,\ r = h \circ q \Rightarrow (\forall y, yPrime,\ \operatorname{secondStageRelation}\left(tau, q, h\right)(piQ(y))(piQ(yPrime)) \iff \operatorname{ker}\left(\operatorname{completeItinerary}\left(tau, r\right)\right)(y, yPrime) \land\ \operatorname{Surjective}\left(kappa\right) \land\ \operatorname{secondStageRelation}\left(tau, q, h\right) = \operatorname{ker}\left(kappa\right) \land\ \exists e: \operatorname{Quotient}(\operatorname{secondStageRelation}\left(tau, q, h\right)) \equiv Zr,\ (\forall state,\ e(mk(state)) = kappa(state)) \land\ \forall y,\ e(mk(piQ(y))) = piR(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/CascadeCompletion.cascade_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the coarse readout be obtained by applying a forgetful map to the fine readout. On the fine predictive completion, compose the current readout with that same map. Equality of every future coarse readout then agrees exactly with equality of the original coarse itineraries on projected states.

The canonical factor from the fine completion to the coarse completion is surjective. Its kernel is precisely the second-stage future relation, so quotienting the fine completion by that relation gives the direct coarse completion.

The quotient equivalence is the pinned Mathlib third isomorphism theorem for setoids. Its value on every second-stage class is the canonical factor, and on an original projected state it is the coarse completion projection.

Repository search found the exact completion factor theorem and the complete-itinerary construction. Pinned Mathlib and Loogle found Setoid.quotientQuotientEquivQuotient, Quotient.map_surjective, Quotient.eq, and Quotient.congrRight; each is applied in the Lean bridge. LeanSearch returned HTTP 404 and no usable result.

**Definition 1.2 (Cascade completion equivalence).**

$$\forall Y \in Type, O \in Type, P \in Type, update \in Y \to Y, fine \in Y \to O, coarse \in Y \to P, forget \in O \to P, hfactor \in coarse = forget \circ fine,\; \operatorname{Quotient}(\operatorname{secondStageRelation}\left(update, fine, forget\right)) \equiv \operatorname{CompletedState}\left(update, coarse\right).$$

*Formalization.* `D5/S3/ObserverMemory/Refinement/CascadeCompletion.cascadeCompletionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical equivalence identifies the quotient by the second-stage relation with the completed coarse state, under the factorization of the coarse readout through the fine readout.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/CascadeCompletion.cascadeCompletionEquiv`
- Truth anchor: `D5/S3/ObserverMemory/Refinement/CascadeCompletion.cascade_completion`
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](PredictionCompletion.md)
