# A One-Dimensional Local-Minimum Counterexample

## Abstract

The one-dimensional interval has connected affine exposed faces but a nonglobal relative local minimum.

**Definition 1.1 (The closed unit interval).**

Lean statement: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.intervalK`

*Formalization.* `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.intervalK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

intervalK is the closed real interval [0,1], which supplies the compact convex model in the one-dimensional obstruction.

**Definition 1.2 (The two pure endpoints).**

Lean statement: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.pureEndpoints`

*Formalization.* `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.pureEndpoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pureEndpoints is the two-point set {0,1}, representing the extreme points of the interval.

**Definition 1.3 (Affine exposed faces).**

Lean statement: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.exposedFace`

*Formalization.* `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.exposedFace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real function g, exposedFace g consists of the points in the interval at which g attains its maximum.

**Definition 1.4 (Relative local minimum).**

Lean statement: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.relativeLocalMinimum`

*Formalization.* `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.relativeLocalMinimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

relativeLocalMinimum records a positive-radius neighborhood inside a set on which the function value is no smaller than at the chosen point.

**Definition 1.5 (Global minimum).**

Lean statement: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.globalMinimum`

*Formalization.* `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.globalMinimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

globalMinimum requires the chosen point to have value no larger than the function value at every point of the set.

**Theorem 1.6 (Connected affine faces do not prevent a nonglobal local minimum).**

$$IsCompact\left(intervalK\right) \land IsCompact\left(pureEndpoints\right) \land \forall m, b: \mathbb{R},\ IsConnected\left(exposedFace\left(Affine\left(m, b\right)\right)\right) \land relativeLocalMinimum\left(coordinate, pureEndpoints, 1\right) \land \neg globalMinimum\left(coordinate, pureEndpoints, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.interval_affine_faces_and_endpoint_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every affine function m x + b, its maximum face on [0,1] is connected: it is the whole interval when m=0 and a singleton endpoint when m is nonzero. The endpoint set itself is compact.

With the coordinate function x restricted to {0,1}, the point 1 is a relative local minimum: a radius-one-half neighborhood in the endpoint set contains no point other than 1. It is not a global minimum because the endpoint 0 has the smaller coordinate.

This is the explicit one-dimensional obstruction from the source: connected pure edges and compactness alone do not turn every relative local minimum into a global minimum.

## References

- Truth anchor: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.exposedFace`
- Truth anchor: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.globalMinimum`
- Truth anchor: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.intervalK`
- Truth anchor: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.interval_affine_faces_and_endpoint_counterexample`
- Truth anchor: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.pureEndpoints`
- Truth anchor: `D5/S3/QuantumContext/IntervalLocalMinimumCounterexample.relativeLocalMinimum`
