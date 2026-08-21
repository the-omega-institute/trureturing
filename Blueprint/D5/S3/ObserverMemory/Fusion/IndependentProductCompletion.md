# Independent Product Completion

## Abstract

Independent product readouts have a product predictive completion and componentwise quotient dynamics.

**Theorem 1.1 (Independent product completion is a product with component dynamics).**

$$\begin{gathered}\forall tau1, tau2, q1, q2,\\\operatorname{Nonempty}(\operatorname{CompletedState}\left(\operatorname{productUpdate}\left(tau1, tau2\right), \operatorname{productReadout}\left(q1, q2\right)\right)\equiv (\operatorname{CompletedState}\left(tau1, q1\right))\times(\operatorname{CompletedState}\left(tau2, q2\right))) \land\\\forall state: \operatorname{CompletedState}\left(\operatorname{productUpdate}\left(tau1, tau2\right), \operatorname{productReadout}\left(q1, q2\right)\right),\\\operatorname{productCompletionMap}\left(tau1, tau2, q1, q2, \operatorname{completionUpdate}\left(\operatorname{productUpdate}\left(tau1, tau2\right), \operatorname{productReadout}\left(q1, q2\right), state\right)\right) = (\operatorname{completionUpdate}\left(tau1, q1, \operatorname{first}\left(\operatorname{productCompletionMap}\left(tau1, tau2, q1, q2, state\right)\right)\right), \operatorname{completionUpdate}\left(tau2, q2, \operatorname{second}\left(\operatorname{productCompletionMap}\left(tau1, tau2, q1, q2, state\right)\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/IndependentProductCompletion.independent_product_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For component state spaces with self-maps tau1 and tau2 and readouts q1 and q2, the product state update and paired readout are constructed pointwise. Each predictive completion is the quotient by equality of all future readout values.

The public equivalence sends a product quotient class to the pair of its component quotient classes. Coordinate equality of complete itineraries makes this map well-defined; representatives of either component give surjectivity, and the two coordinate quotient equalities give injectivity.

The induced update on the product quotient is carried by this equivalence to the pair of the two component quotient updates, which is the source's independent direct-product dynamics.

Pinned repository hits CompletedState, completionProjection, completionUpdate, and completeItinerary are imported and applied directly. Quotient lift, soundness, exactness, and Equiv.ofBijective are the pinned primitives; no exact independent-product completion theorem was found.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/IndependentProductCompletion.independent_product_completion`
- Dependency: [D5/S3/ObserverMemory/Refinement/PredictionCompletion](../Refinement/PredictionCompletion.md)
