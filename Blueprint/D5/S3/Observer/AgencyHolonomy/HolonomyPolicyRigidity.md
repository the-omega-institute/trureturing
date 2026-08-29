# Holonomy Policy Rigidity

## Abstract

An injective policy invariant under holonomy forces trivial holonomy.

**Theorem 1.1 (An injective invariant policy forces identity holonomy).**

$$\forall policy: M \to A, h: M \to M, (\operatorname{Injective}\left(policy\right) \land (\forall m: M, \operatorname{policy}\left(\operatorname{h}\left(m\right)\right) = \operatorname{policy}\left(m\right))) \Rightarrow h = id.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/HolonomyPolicyRigidity.policy_invariant_holonomy_eq_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a policy is injective in memory and invariant under a memory holonomy at every state.

Injectivity reflects each invariant policy equality to a fixed-point equality. Extensionality makes the holonomy the identity.

**Theorem 1.2 (No nontrivial invisible loop remains at any state).**

$$\forall policy: M \to A, h: M \to M, m: M, (\operatorname{Injective}\left(policy\right) \land (\forall m: M, \operatorname{policy}\left(\operatorname{h}\left(m\right)\right) = \operatorname{policy}\left(m\right))) \Rightarrow \operatorname{h}\left(m\right) = m.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/HolonomyPolicyRigidity.no_nontrivial_invisible_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same injectivity and pointwise invariance assumptions, fix one memory state.

The policy equality at that state forces the transported memory to equal the original memory. The claim is pointwise, not a new converse.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/HolonomyPolicyRigidity.no_nontrivial_invisible_loop`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/HolonomyPolicyRigidity.policy_invariant_holonomy_eq_identity`
