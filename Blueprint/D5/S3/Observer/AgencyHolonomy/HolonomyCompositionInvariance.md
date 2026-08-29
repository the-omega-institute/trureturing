# Holonomy Composition Invariance

## Abstract

Policy-invisible memory transports are closed under composition.

**Theorem 1.1 (Invisible transports compose).**

$$\forall policy: M \to A, first, second: M \to M,\\{}(\operatorname{PolicyInvisible}\left(policy, first\right) \land \operatorname{PolicyInvisible}\left(policy, second\right)) \Rightarrow \operatorname{PolicyInvisible}\left(policy, second \circ first\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/HolonomyCompositionInvariance.invisible_transports_compose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume first and second each preserve the policy value at every memory state.

Apply second's invariance after first, then first's invariance. Their composite is therefore policy-invisible at every memory.

**Theorem 1.2 (Identity transport is invisible).**

$$\forall policy: M \to A, \operatorname{PolicyInvisible}\left(policy, id\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/HolonomyCompositionInvariance.identity_transport_invisible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity memory transport leaves every memory state unchanged.

It is consequently policy-invisible for every policy, without any additional hypothesis.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/HolonomyCompositionInvariance.identity_transport_invisible`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/HolonomyCompositionInvariance.invisible_transports_compose`
