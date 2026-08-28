# Dual Observer Distance Readings

## Abstract

Two bounded-function observers assign a typed extended-distance reading to the same endpoints.

**Theorem 1.1 (One endpoint pair has two typed observer readings).**

$$\begin{aligned}\forall X: Type, A, APrime: \operatorname{Submodule}(\mathbb{R}, \operatorname{ellInfty}(X, \mathbb{R})),\\{}L: A \to [0, \infty], LPrime: APrime \to [0, \infty], x, y: X,\\{}(\forall c: \mathbb{R}, f: A, L(cf) = \left|c\right|L(f)) \land (\forall c: \mathbb{R}, f: APrime, LPrime(cf) = \left|c\right|LPrime(f)) \Rightarrow\\{}\operatorname{let} d_{O} = \operatorname{observerDistance}(A, L, x, y);\\{}\operatorname{let} d_{OPrime} = \operatorname{observerDistance}(APrime, LPrime, x, y);\\{}\operatorname{let} Z_{O} = \operatorname{span}(\mathbb{R}, \operatorname{unitBall}(A, L)) = A \Rightarrow (d_{O} = 0 \iff \forall f \in A, f(x) = f(y));\\{}\operatorname{let} Z_{OPrime} = \operatorname{span}(\mathbb{R}, \operatorname{unitBall}(APrime, LPrime)) = APrime \Rightarrow (d_{OPrime} = 0 \iff \forall f \in APrime, f(x) = f(y));\\{}\operatorname{let} H_{O} = (\exists f \in A, L(f) = 0 \land f(x) \neq f(y)) \Rightarrow d_{O} = \infty;\\{}\operatorname{let} H_{OPrime} = (\exists f \in APrime, LPrime(f) = 0 \land f(x) \neq f(y)) \Rightarrow d_{OPrime} = \infty\\{}\operatorname{in} ((d_{O} = 0 \land Z_{O} \land H_{O}) \lor (0 < d_{O} < \infty \land Z_{O} \land H_{O}) \lor (d_{O} = \infty \land Z_{O} \land H_{O})) \land ((d_{OPrime} = 0 \land Z_{OPrime} \land H_{OPrime}) \lor (0 < d_{OPrime} < \infty \land Z_{OPrime} \land H_{OPrime}) \lor (d_{OPrime} = \infty \land Z_{OPrime} \land H_{OPrime})).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/DualObserverDistanceReadings.dual_observer_distance_readings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observable carriers are real subspaces of the bounded functions on the state set. Each cost is homogeneous under real scaling, and each distance is the supremum of endpoint gaps over its unit-cost ball.

When that unit ball spans its observable space, zero distance is exactly equality of all accessible readouts. A zero-cost observable that separates the endpoints can be scaled without cost and therefore forces infinite distance.

## References

- Truth anchor: `D5/S3/ContinuousObservables/DualObserverDistanceReadings.dual_observer_distance_readings`
- Dependency: [D5/S3/Observer/Separation/RefinementDistanceMonotonicity](../Observer/Separation/RefinementDistanceMonotonicity.md)
