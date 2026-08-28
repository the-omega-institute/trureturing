# Family-Indexed Product Completion

## Abstract

Finite independent readouts have a product completion and pointwise dynamics.

**Theorem 1.1 (The predictive completion of a finite product is the product of the completions).**

$$\begin{gathered}\forall I: \operatorname{Type}, [\operatorname{Fintype}(I)],\\{}Y, O: I \to \operatorname{Type},\\{}tau: \forall i\in I, \operatorname{Y}\left(i\right) \to \operatorname{Y}\left(i\right), q: \forall i\in I, \operatorname{Y}\left(i\right) \to \operatorname{O}\left(i\right),\\{}\operatorname{let}(e = \operatorname{familyProductCompletionEquiv}\left(tau, q\right): \operatorname{CompletedState}\left(\operatorname{pointwiseUpdate}\left(tau\right), \operatorname{pointwiseReadout}\left(q\right)\right) \equiv \prod_{i \in I} \operatorname{CompletedState}\left(\operatorname{tau}\left(i\right), \operatorname{q}\left(i\right)\right)),\\{}(\forall y: \prod_{i \in I} \operatorname{Y}\left(i\right), e(\operatorname{completionProjection}\left(\operatorname{pointwiseUpdate}\left(tau\right), \operatorname{pointwiseReadout}\left(q\right), y\right)) = (i \mapsto \operatorname{completionProjection}\left(\operatorname{tau}\left(i\right), \operatorname{q}\left(i\right), y(i)\right))) \land\\{}(\forall z: \operatorname{CompletedState}\left(\operatorname{pointwiseUpdate}\left(tau\right), \operatorname{pointwiseReadout}\left(q\right)\right), e(\operatorname{completionUpdate}\left(\operatorname{pointwiseUpdate}\left(tau\right), \operatorname{pointwiseReadout}\left(q\right), z\right)) = (i \mapsto \operatorname{completionUpdate}\left(\operatorname{tau}\left(i\right), \operatorname{q}\left(i\right), e(z)(i)\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/FamilyIndexedProductCompletion.family_indexed_product_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite index type carries dependent state and output families. The global update and readout are constructed pointwise from the component maps, and CompletedState is the canonical quotient by equality of complete future readout itineraries.

The named canonical equivalence sends the class of a configuration to the family of its coordinate classes. The first public law records this projection computation directly.

The second public law says that applying the induced global update before the equivalence is exactly the family of component completion updates.

Pinned repository primitives CompletedState, completionProjection, completionUpdate, and completeItinerary are imported and applied. Pinned Mathlib's exact Setoid.piQuotientEquiv is composed with Quotient.congrRight; no family-indexed repository theorem was found.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/FamilyIndexedProductCompletion.family_indexed_product_completion`
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](../Refinement/PredictionCompletion.md)
