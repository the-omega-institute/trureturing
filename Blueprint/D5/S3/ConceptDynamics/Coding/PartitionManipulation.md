# Partition Manipulation

## Abstract

Homogeneous message fibers admit a correct default rule and exclude partition manipulation.

**Theorem 1.1 (Homogeneous message fibers exclude partition manipulation).**

$$\forall X \in Type, M \in Type, Tval \in Type,\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall message \in X \to M, target \in X \to Tval,\; \left(\forall a \in X, b \in X,\; message\left(a\right) = message\left(b\right) \Rightarrow target\left(a\right) = target\left(b\right)\right) \Rightarrow \left(\exists delta \in M \to Tval,\; \left(\forall actual \in X,\; delta\left(message\left(actual\right)\right) = target\left(actual\right)\right) \land \left(\forall actual \in X,\; \neg \operatorname{PartitionManipulation}\left(message, target, delta, actual\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PartitionManipulation.manipulation_needs_heterogeneous_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose two states with the same message always have the same target value. Nonemptiness supplies an anchor target value, allowing the target on realized messages to extend to a total default rule on the whole message space.

The resulting default agrees with the target at every actual state. Partition manipulation requires the default at the true message to be wrong, so this pointwise agreement rules it out everywhere.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PartitionManipulation.manipulation_needs_heterogeneous_fiber`
- Dependency: [D5/S0/Rewriting/Quotients/AnswerabilityCriterion](../../../S0/Rewriting/Quotients/AnswerabilityCriterion.md)
