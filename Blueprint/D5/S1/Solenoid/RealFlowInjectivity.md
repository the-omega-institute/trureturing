# Universal-Solenoid Real-Flow Injectivity

## Abstract

The universal-solenoid real flow is faithful.

**Theorem 1.1 (The real flow has trivial kernel).**

$$\forall t \in \mathbb{R},\  realFlow(t) = 0 \iff t = 0.$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/RealFlowInjectivity.realFlow_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the flow vanishes, then at every positive modulus its coordinate t divided by that modulus is an integer modulo one. Choose a natural modulus larger than the absolute value of t. The corresponding integer has absolute value below one, hence is zero, and division by the positive modulus forces t to vanish. The converse is the established zero law for the real flow.

The pinned library supplies the additive-circle zero criterion, the Archimedean natural bound, and the integer absolute-value lemma. The repository's coordinate formula assembles them into the universal-solenoid kernel criterion.

**Theorem 1.2 (The real flow is injective).**

$$\operatorname{Injective}(realFlow).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/RealFlowInjectivity.realFlow_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing real-flow additive homomorphism is injective exactly when its kernel is trivial. Applying the preceding kernel criterion therefore proves faithfulness of the real action.

## References

- Truth anchor: `D5/S1/Solenoid/RealFlowInjectivity.realFlow_eq_zero_iff`
- Truth anchor: `D5/S1/Solenoid/RealFlowInjectivity.realFlow_injective`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](../Dynamics/UniversalSolenoid.md)
