# Product Completion Depth Upper Bound

## Abstract

The maximum local completion depth completes a pointwise product observer.

**Theorem 1.1 (The slowest local completion depth suffices for the product).**

$$\forall I: \operatorname{Type}, Y, O: I \to \operatorname{Type},\\{}F: \forall i\in I, \operatorname{Y}\left(i\right) \to \operatorname{Y}\left(i\right), q: \forall i\in I, \operatorname{Y}\left(i\right) \to \operatorname{O}\left(i\right), m: I \to \mathbb{N},\\{}\operatorname{Fintype}\left(I\right) \land (\forall i\in I, \forall x, y\in \operatorname{Y}\left(i\right), \operatorname{word}\left(F, q, i, \operatorname{m}\left(i\right), x\right) = \operatorname{word}\left(F, q, i, \operatorname{m}\left(i\right), y\right) \Rightarrow \operatorname{itinerary}\left(F, q, i, x\right) = \operatorname{itinerary}\left(F, q, i, y\right)) \Rightarrow\\{}\forall x, y\in \prod_{i \in I} \operatorname{Y}\left(i\right), \operatorname{word}\left(\operatorname{pointwiseUpdate}\left(F\right), \operatorname{pointwiseReadout}\left(q\right), \operatorname{finiteMax}\left(I, m\right), x\right) = \operatorname{word}\left(\operatorname{pointwiseUpdate}\left(F\right), \operatorname{pointwiseReadout}\left(q\right), \operatorname{finiteMax}\left(I, m\right), y\right) \Rightarrow \operatorname{itinerary}\left(\operatorname{pointwiseUpdate}\left(F\right), \operatorname{pointwiseReadout}\left(q\right), x\right) = \operatorname{itinerary}\left(\operatorname{pointwiseUpdate}\left(F\right), \operatorname{pointwiseReadout}\left(q\right), y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/ProductCompletionDepthUpperBound.product_completion_depth_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite index type carries dependent state and output families, with one update, readout, and completion depth at every coordinate.

The sole semantic premise says that each local word through its stated depth determines that factor's complete itinerary. No sharp witness, least-depth assumption, or nonemptiness premise is required.

The global update and readout are the pointwise products of the local maps. Equality of their word through the finite maximum restricts to equality of every local word, so the local completion laws give equality of the complete product itineraries.

Repository primitives futureReadoutWord and completeItinerary are used directly. The sharper product-depth equality theorem is not applied because its witness premises are absent from this upper-bound claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/ProductCompletionDepthUpperBound.product_completion_depth_upper_bound`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
