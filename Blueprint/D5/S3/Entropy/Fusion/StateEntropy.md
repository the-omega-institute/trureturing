# Fusion State Entropy

## Abstract

Fusion-state entropy equals joint prediction entropy and both Shannon chain-rule forms.

**Theorem 1.1 (Fusion-state entropy has both chain-rule forms).**

$$\begin{gathered}\forall Y, Z1, Z2, Z12,\\p: Y \to \mathbb{R}, pi12: Y \to Z12,\\pi1: Y \to Z1, pi2: Y \to Z2,\\J: Z12 \to Z1\times Z2,\\\operatorname{nonnegative}\left(p\right) \land \operatorname{Surjective}\left(pi12\right) \land \operatorname{Injective}\left(J\right) \land\\\forall y\in Y, J(pi12(y)) = \operatorname{pair}\left(pi1, pi2\right)(y) \Rightarrow\\\operatorname{H}\left(\operatorname{push}\left(pi12, p\right)\right) = \operatorname{H}\left(\operatorname{push}\left(\operatorname{pair}\left(pi1, pi2\right), p\right)\right) \land\\\operatorname{H}\left(\operatorname{push}\left(pi12, p\right)\right) = \operatorname{H}\left(\operatorname{push}\left(pi1, p\right)\right) + \operatorname{Hcond}\left(\operatorname{push}\left(\operatorname{pair}\left(pi1, pi2\right), p\right)\right) \land\\\operatorname{H}\left(\operatorname{push}\left(pi12, p\right)\right) = \operatorname{H}\left(\operatorname{push}\left(pi2, p\right)\right) + \operatorname{Hcond}\left(\operatorname{swap}\left(\operatorname{push}\left(\operatorname{pair}\left(pi1, pi2\right), p\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Fusion/StateEntropy.fusion_state_entropy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite source state space with a nonnegative mass function. The maps pi12, pi1, and pi2 produce the fused and component prediction states, while J maps the fused state into the pair of component states.

Assume pi12 is onto, J is injective, and J(pi12(y)) equals (pi1(y), pi2(y)) for every source state. The source-semantic pushforward laws then identify the fused law with the jointly predicted pair law up to the injective relabeling J.

Entropy invariance under injective relabeling gives the first equality. Applying the finite Shannon chain rule to the pair law, and then to its coordinate swap, gives the two displayed conditional-entropy decompositions.

## References

- Truth anchor: `D5/S3/Entropy/Fusion/StateEntropy.fusion_state_entropy_identity`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/MutualInformationSymm](../MutualInformationSymm.md)
- Dependency: [D5/S3/Entropy/Relabeling/InjectiveInvariance](../Relabeling/InjectiveInvariance.md)
