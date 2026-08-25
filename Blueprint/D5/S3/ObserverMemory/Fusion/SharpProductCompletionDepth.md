# Sharp Product Completion Depth

## Abstract

Sharp local witnesses give the maximum law for finite product completion depth.

**Theorem 1.1 (The slowest sharp local factor fixes the product completion depth).**

$$\forall I: \operatorname{Type}, Y, O: I \to \operatorname{Type},\\{}F: \forall i\in I, \operatorname{Y}\left(i\right) \to \operatorname{Y}\left(i\right), q: \forall i\in I, \operatorname{Y}\left(i\right) \to \operatorname{O}\left(i\right), m: I \to \mathbb{N},\\{}\operatorname{Fintype}\left(I\right) \land \operatorname{Fintype}\left(\prod_{i \in I} \operatorname{Y}\left(i\right)\right) \land (\forall i\in I, \operatorname{Nonempty}\left(\operatorname{Y}\left(i\right)\right)) \land\\{}(\forall i\in I, 0 < \operatorname{m}\left(i\right) \Rightarrow \forall x, y\in \operatorname{Y}\left(i\right), \operatorname{word}\left(F, q, i, \operatorname{m}\left(i\right), x\right) = \operatorname{word}\left(F, q, i, \operatorname{m}\left(i\right), y\right) \Rightarrow \operatorname{itinerary}\left(F, q, i, x\right) = \operatorname{itinerary}\left(F, q, i, y\right)) \land\\{}(\forall i\in I, 0 < \operatorname{m}\left(i\right) \Rightarrow \exists x, y\in \operatorname{Y}\left(i\right), \operatorname{word}\left(F, q, i, \operatorname{m}\left(i\right) - 1, x\right) = \operatorname{word}\left(F, q, i, \operatorname{m}\left(i\right) - 1, y\right) \land \operatorname{itineraryAt}\left(F, q, i, x, \operatorname{m}\left(i\right)\right) \neq \operatorname{itineraryAt}\left(F, q, i, y, \operatorname{m}\left(i\right)\right)) \land\\{}(\forall i\in I, \operatorname{m}\left(i\right) = 0 \Rightarrow \forall x, y\in \operatorname{Y}\left(i\right), \operatorname{q}\left(i, x\right) = \operatorname{q}\left(i, y\right) \Rightarrow \operatorname{itinerary}\left(F, q, i, x\right) = \operatorname{itinerary}\left(F, q, i, y\right)) \Rightarrow\\{}\operatorname{observationStabilityDepth}\left(\operatorname{pointwiseUpdate}\left(F\right), \operatorname{pointwiseReadout}\left(q\right)\right) = \operatorname{finiteMax}\left(I, m\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/SharpProductCompletionDepth.sharp_product_completion_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite index set carries dependent state and output families. The full dependent product of state carriers is finite, and every component state carrier is nonempty so a local witness can be embedded while all other coordinates remain fixed.

At every positive local depth, the finite word already determines the complete itinerary and a pair agrees through the preceding depth but differs at the stated depth. At local depth zero, equality of the current readout determines the complete itinerary.

The update and readout on the independent product are constructed pointwise from the component maps. The canonical least observation stability depth of that product is the finite maximum of the local depths.

The proof applies the existing exact semantics of shortest distance. Every global first mismatch is bounded by its differing coordinate, and every positive sharp local witness embeds as a global pair with the same first mismatch.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/SharpProductCompletionDepth.sharp_product_completion_depth`
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/ShortestDistanceSemantics](../PredictionCertificates/ShortestDistanceSemantics.md)
