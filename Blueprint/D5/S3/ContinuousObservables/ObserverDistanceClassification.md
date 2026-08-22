# Observer Distance Classification

## Abstract

Invariant leaves are infinitely separated, while cyclic and integer leaves recover their source path distances.

**Theorem 1.1 (Invariant leaves classify observer distance).**

$$\forall I, Leaf,\ \forall tau \in \operatorname{EquivPerm}(I), \forall leaf \in \operatorname{Map}(I, Leaf), \forall x, y \in I,\ \operatorname{InvariantLeaf}(tau, leaf) \land leaf(x) \neq leaf(y) \Rightarrow \operatorname{observerDistance}(tau, x, y) = \operatorname{top} \land \forall M \in \mathbb{N}, a, b \in \operatorname{ZMod}(M),\ \operatorname{windowObserverDistance}(M, a, b) = \operatorname{windowCycleDist}(M, a, b) \land \forall m, n \in \mathbb{Z},\ \operatorname{orbitConnesDistance}(m, n) = \left|(n-m)\right|.$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/ObserverDistanceClassification.permutation_observer_distance_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admissible readouts are bounded real functions whose one-step update defect is at most one. An invariant leaf indicator is bounded, unchanged by the update, and separates distinct leaves; scaling it makes the extended supremum infinite.

The finite cyclic clause is the exact repository theorem for the window observer distance. The bounded integer clause is the exact orbit Connes distance computation, so both source path metrics are exposed without redefining them.

The three clauses are deposited together as the public conjunction required by the source statement.

## References

- Truth anchor: `D5/S3/ContinuousObservables/ObserverDistanceClassification.permutation_observer_distance_classification`
- Dependency: [D5/S3/Observer/MetricGeometry/OrbitConnesDistance](../Observer/MetricGeometry/OrbitConnesDistance.md)
- Dependency: [D5/S3/Observer/MetricGeometry/WindowObserverDistance](../Observer/MetricGeometry/WindowObserverDistance.md)
