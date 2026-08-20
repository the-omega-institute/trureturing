# Continuous Discrete Rigidity

## Abstract

Every continuous map from a connected space to a discrete space is constant.

**Theorem 1.1 (A continuous map from connected to discrete is constant).**

$$\forall X, Y: \operatorname{Type},\ [\operatorname{TopologicalSpace}(X)], [\operatorname{ConnectedSpace}(X)],\ [\operatorname{TopologicalSpace}(Y)], [\operatorname{DiscreteTopology}(Y)],\ T: X \to Y, \operatorname{Continuous}(T) \Rightarrow\\\forall x, y: X, T(x) = T(y).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/Connectivity/ContinuousDiscreteRigidity.continuous_map_to_discrete_is_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be connected and Y carry the discrete topology. For an arbitrary continuous map T from X to Y, any two values T(x) and T(y) are equal.

Pinned Mathlib supplies PreconnectedSpace.constant, which is applied directly after connectedness supplies the preconnected-space instance. Repository search found no duplicate map theorem.

## References

- Truth anchor: `D5/S1/Solenoid/Connectivity/ContinuousDiscreteRigidity.continuous_map_to_discrete_is_constant`
