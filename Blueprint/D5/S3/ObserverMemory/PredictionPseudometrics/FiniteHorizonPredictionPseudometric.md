# Finite-Horizon Prediction Pseudometric

## Abstract

Finite prediction distance is a pseudometric whose kernel is finite future agreement.

**Theorem 1.1 (Finite prediction distance detects finite future agreement).**

$$D_{T}(x, y) = \max_{0 \leq t \leq T} d_{Z}(\pi U_{t} x, \pi U_{t} y) \land\\D_{T}(x, x) = 0 \land\\D_{T}(x, y) = D_{T}(y, x) \land\\D_{T}(x, y) \leq D_{T}(x, z) + D_{T}(z, y) \land\\D_{T}(x, y) = 0 \Leftrightarrow \forall t \leq T, \pi U_{t} x = \pi U_{t} y \land\\\exists x, y, \operatorname{RawDistance}\left(x, y\right) = 100 \land D_{T}(x, y) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.finite_horizon_prediction_pseudometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any state type, including an empty one, and any metric output type, take the existing finite prediction distance at unit discount through time T. No global output-distance bound is required; the index type Fin(T+1) is finite and nonempty.

Finite Bellman recursion identifies this distance with the finite product sup metric on the readout word from time zero through T. That metric supplies the displayed maximum formula, zero on the diagonal, symmetry, and the triangle inequality.

Distance zero is equivalent to the imported finite-future relation. Compiled Empty-state and real-valued observer instances verify that neither state inhabitation nor ambient boundedness has been smuggled back into the finite theorem.

A checked finite witness changes a hidden coordinate from zero to one hundred while retaining the same constant observer readout. Its raw coordinate distance is one hundred and its prediction distance is zero, separating correlation mass from observer influence.

**Theorem 1.2 (Bounded infinite prediction distance detects complete itineraries).**

$$D_{\infty}(x, y) = 0 \Leftrightarrow \operatorname{InfiniteFutureRelation}\left(x, y\right) \land\\D_{\infty}(x, y) = 0 \Leftrightarrow \operatorname{CompleteItinerary}\left(x\right) = \operatorname{CompleteItinerary}\left(y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.bounded_infinite_horizon_prediction_zero_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the undiscounted infinite supremum, assume a global bound on output distances. Under exactly this boundedness hypothesis, prediction distance zero is equivalent both to the imported infinite-future relation and to equality in the complete-itinerary kernel.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.bounded_infinite_horizon_prediction_zero_kernel`
- Truth anchor: `D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.finite_horizon_prediction_pseudometric`
- Dependency: [D5/S3/Observer/MetricGeometry/FinitePredictionTruncation](../../Observer/MetricGeometry/FinitePredictionTruncation.md)
- Dependency: [D5/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric](../../Observer/MetricGeometryLaws/DiscountedPredictionPseudometric.md)
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../../Observer/Separation/FiniteFutureCongruence.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
