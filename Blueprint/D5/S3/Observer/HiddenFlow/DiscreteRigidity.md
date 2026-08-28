# Integer Actions Obstruct Continuous Hidden Flows

## Abstract

Nonzero integer-parameter hidden actions cannot extend to continuous additive real flows.

**Theorem 1.1 (Nonzero integer actions have no continuous real extension).**

$$HiddenAddress := \prod_{p \in \mathbb{P}} \mathbb{Z}_{p};\ \forall jump \in \operatorname{AddHom}(\mathbb{Z}, HiddenAddress), jump \neq 0 \Rightarrow \neg \exists flow \in \operatorname{CAddHom}(\mathbb{R}, HiddenAddress), flow \circ cast_{\mathbb{Z}} = jump.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/DiscreteRigidity.nonzero_integer_action_has_no_continuous_real_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let jump be an additive integer-parameter action on the hidden address space. If a continuous additive real flow restricted along the canonical integer inclusion to jump, the frozen continuous-rigidity theorem would make that real flow zero. Its integer restriction would then be zero as well, contradicting the nonzero hypothesis.

This establishes an obstruction for each named nonzero integer action itself. It does not say that every action has integer parameters, that every hidden-address subgroup is cyclic, that a minimal jump exists, or that an observer premise selects an action.

**Theorem 1.2 (The canonical integer jump is nonzero and has no real extension).**

$$discreteHiddenJump \neq 0 \land \neg \exists flow \in \operatorname{CAddHom}(\mathbb{R}, \prod_{p \in \mathbb{P}} \mathbb{Z}_{p}), flow \circ cast_{\mathbb{Z}} = discreteHiddenJump.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/DiscreteRigidity.discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical jump sends each integer to its cast in every p-adic coordinate. Its value at one in the prime-two coordinate is one, so it is nonzero. Applying the preceding obstruction to this same map proves that no continuous additive real flow restricts to it.

The conjunction supplies the required anti-vacuity witness and derives its separation from real flows from rigidity. It makes no crossed-product universal-property claim and no classification claim for other actions.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/DiscreteRigidity.discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension`
- Truth anchor: `D5/S3/Observer/HiddenFlow/DiscreteRigidity.nonzero_integer_action_has_no_continuous_real_extension`
- Dependency: [D5/S3/Observer/HiddenFlow/ContinuousRigidity](ContinuousRigidity.md)
