# Finite-Horizon Prediction Pseudometric

## Abstract

Finite prediction distance is a pseudometric whose kernel is finite future agreement.

**Theorem 1.1 (Finite prediction distance detects finite future agreement).**

$$D_{T}(x, y) = \max_{0 \leq t \leq T} d_{Z}(\pi U_{t} x, \pi U_{t} y) \land\\D_{T}(x, x) = 0 \land\\D_{T}(x, y) = D_{T}(y, x) \land\\D_{T}(x, y) \leq D_{T}(x, z) + D_{T}(z, y) \land\\D_{T}(x, y) = 0 \Leftrightarrow \forall t \leq T, \pi U_{t} x = \pi U_{t} y \land\\D_{\infty}(x, y) = 0 \Leftrightarrow \operatorname{CompleteItinerary}\left(x\right) = \operatorname{CompleteItinerary}\left(y\right) \land\\\exists x, y, \operatorname{RawDistance}\left(x, y\right) = 100 \land D_{T}(x, y) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.finite_horizon_prediction_pseudometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty state type and a metric output type, take the existing finite prediction distance at unit discount through time T. The output-distance bound is an explicit hypothesis, while the index type Fin(T+1) makes the horizon finite and nonempty.

The imported finite-truncation theorem identifies this distance with the maximum of the observer-output distances from time zero through T. The finite product sup metric then supplies zero on the diagonal, symmetry, and the triangle inequality.

Distance zero is equivalent to the imported finite-future relation. At infinite horizon, unit-discount prediction distance has zero kernel exactly when the imported complete itineraries agree, which is the relation underlying predictive completion.

A checked finite witness changes a hidden coordinate from zero to one hundred while retaining the same constant observer readout. Its raw coordinate distance is one hundred and its prediction distance is zero, separating correlation mass from observer influence.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.finite_horizon_prediction_pseudometric`
- Dependency: [D5/S3/Observer/MetricGeometry/FinitePredictionTruncation](../../Observer/MetricGeometry/FinitePredictionTruncation.md)
- Dependency: [D5/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric](../../Observer/MetricGeometryLaws/DiscountedPredictionPseudometric.md)
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../../Observer/Separation/FiniteFutureCongruence.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
