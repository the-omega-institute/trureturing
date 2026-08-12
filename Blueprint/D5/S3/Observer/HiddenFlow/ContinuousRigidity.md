# Continuous Hidden-Flow Rigidity

## Abstract

Continuous additive real flows in the observer hidden-address space are trivial; the canonical integer-cast jump is a separate nonzero witness.

**Theorem 1.1 (Every continuous additive real hidden flow is zero).**

$$\forall \phi \in \operatorname{CAddHom}(\mathbb{R}, \prod_{p \in \mathbb{P}} \mathbb{Z}_{p}), \phi = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/ContinuousRigidity.continuous_hidden_flow_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden address space is the product of the rings of p-adic integers over all primes. A continuous additive homomorphism from the real line into this product is constant because the source is connected and the target is totally disconnected. Additivity fixes the value at the identity parameter to zero, so the constant flow is exactly the zero homomorphism.

This is a flow-level specialization of the repository's existing hidden-fiber rigidity theorem. It excludes a nontrivial continuous real parameterization of hidden address shifts. Its conclusion is only continuous real-flow exclusion: it does not classify all parameter groups, force a nontrivial action to be discrete or integer-valued, assert a crossed-product identification, or show that an observer premise selects this address space.

**Theorem 1.2 (The canonical integer-cast hidden jump is nonzero).**

$$discreteHiddenJump \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/ContinuousRigidity.discreteHiddenJump_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The additive homomorphism sends an integer to its canonical cast in every p-adic coordinate. Evaluating at the integer one and the prime two gives one, which is nonzero. This is only an anti-vacuity witness for one chosen integer-parameter homomorphism. It is independent of the rigidity proof and does not show that every nontrivial hidden action is discrete, integer-valued, or selected by the observer premise.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/ContinuousRigidity.continuous_hidden_flow_eq_zero`
- Truth anchor: `D5/S3/Observer/HiddenFlow/ContinuousRigidity.discreteHiddenJump_ne_zero`
- Dependency: [D5/S3/Arith/HiddenFiberRigidity](../../Arith/HiddenFiberRigidity.md)
- Dependency: [D5/S3/Observer/StreamlineTheorem](../StreamlineTheorem.md)
