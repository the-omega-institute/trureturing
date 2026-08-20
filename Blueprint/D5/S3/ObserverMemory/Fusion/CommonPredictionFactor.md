# Common Prediction Factor

## Abstract

The dynamics-stable common prediction quotient has a unique surjective factor.

**Theorem 1.1 (The common prediction factor has the universal property).**

$$\begin{gathered}\forall Y, O_{1}, O_{2}, W,\\u: Y \to Y, v: W \to W,\\q_{1}: Y \to O_{1}, q_{2}: Y \to O_{2},\\r: Y \to W, \operatorname{Surjective}\left(r\right),\\r \circ u = v \circ r,\\a_{1}: \operatorname{Quotient}(\operatorname{KerTr}\left(u, q_{1}\right)) \to W, a_{2}: \operatorname{Quotient}(\operatorname{KerTr}\left(u, q_{2}\right)) \to W,\\r = a_{1} \circ \pi_{q_{1}}, r = a_{2} \circ \pi_{q_{2}} \Rightarrow\\\exists! h: \operatorname{Quotient}(\operatorname{StableJoin}\left(u, \operatorname{KerTr}\left(u, q_{1}\right), \operatorname{KerTr}\left(u, q_{2}\right)\right)) \to W, \operatorname{Surjective}\left(h\right) \land\\r = h \circ \pi_{common}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/CommonPredictionFactor.common_prediction_factor_universal_property` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let u update source states, and let q1 and q2 be readouts. Each readout determines the canonical complete-itinerary kernel. Their common relation is constructed as the least equivalence relation containing both kernels and preserved by u.

Suppose a surjection r onto W intertwines u with an update v on W. Also suppose r factors through each complete-itinerary quotient by maps a1 and a2. Then there is a unique surjective map h from the common quotient to W, and h factors the canonical projection.

The two given factorizations put both itinerary kernels inside the kernel of r, while the intertwining equation makes that kernel stable under u. The infimum construction therefore lies inside the kernel of r. Pinned Mathlib quotient lift, surjectivity, and uniqueness results then supply the asserted map directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/CommonPredictionFactor.common_prediction_factor_universal_property`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
