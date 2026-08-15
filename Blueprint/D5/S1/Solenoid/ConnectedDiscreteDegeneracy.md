# Connected Discrete Degeneracy

## Abstract

A nonempty connected discrete topological space has exactly one point.

**Theorem 1.1 (A connected discrete space has exactly one point).**

$$\forall X: \operatorname{Type},\ \operatorname{TopologicalSpace}(X), \operatorname{ConnectedSpace}(X), \operatorname{DiscreteTopology}(X) \Rightarrow \exists x: X, \forall y: X, y = x.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/ConnectedDiscreteDegeneracy.connected_discrete_has_unique_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a type equipped with a topology. Assume X is nonempty and connected, and that its topology is discrete.

Mathlib's PreconnectedSpace.trivial_of_discrete supplies the subsingleton property. ConnectedSpace supplies a point of X, so that point is equal to every point of X.

Loogle and LeanSearch both identified PreconnectedSpace.trivial_of_discrete as the exact library result. Repository search found no duplicate D5 theorem.

## References

- Truth anchor: `D5/S1/Solenoid/ConnectedDiscreteDegeneracy.connected_discrete_has_unique_point`
