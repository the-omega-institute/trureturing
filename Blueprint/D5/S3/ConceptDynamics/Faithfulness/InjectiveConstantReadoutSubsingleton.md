# Injective Constant Readout Subsingleton

## Abstract

An injective constant readout has a subsingleton source.

**Theorem 1.1 (An injective constant readout forces a subsingleton source).**

$$\forall q: X \to Y, (\operatorname{Injective}\left(q\right) \land (\forall x, y: X, \operatorname{q}\left(x\right) = \operatorname{q}\left(y\right))) \Rightarrow \operatorname{Subsingleton}\left(X\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/InjectiveConstantReadoutSubsingleton.injective_constant_readout_subsingleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a readout from X to Y that is both injective and constant on every pair of source states.

Constancy equates the readouts of any two states, and injectivity reflects that equality back to the states themselves.

Thus X has at most one element. No inhabitedness or finiteness of X is assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/InjectiveConstantReadoutSubsingleton.injective_constant_readout_subsingleton`
