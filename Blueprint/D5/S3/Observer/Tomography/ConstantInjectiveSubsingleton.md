# Constant Injective Subsingleton

## Abstract

An injective constant readout forces its state carrier to be a subsingleton.

**Theorem 1.1 (A constant injective readout has at most one state).**

$$\forall X, Y: \operatorname{Type},\ \forall q: X \to Y,\ \operatorname{Injective}(q) \land {\forall x, y\in X, \operatorname{q}(x) = \operatorname{q}(y)} \Rightarrow \operatorname{Subsingleton}(X).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/ConstantInjectiveSubsingleton.constant_injective_subsingleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a readout from an arbitrary state type X to an arbitrary codomain Y. Assume independently that q is injective and that all of its values are equal.

Constantness equates the readouts of any two states, and injectivity then equates the states themselves. Thus X is a subsingleton, which directly states that X has at most one element.

Pinned Mathlib's Injective.subsingleton theorem assumes the entire codomain is a subsingleton and therefore is not an exact source match. Repository and pinned-library searches found no exact theorem with the two displayed premises.

The subsequent source discussion about replacing one scalar readout by a binary structure is qualitative and supplies no in-scope binary-structure predicate, so it is not promoted to a conjunct.

## References

- Truth anchor: `D5/S3/Observer/Tomography/ConstantInjectiveSubsingleton.constant_injective_subsingleton`
