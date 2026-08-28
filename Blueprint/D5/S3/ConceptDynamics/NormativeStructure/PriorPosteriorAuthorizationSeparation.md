# Prior and Posterior Authorization Separation

## Abstract

A change can revise the standard by which the changed subject later authorizes it.

**Theorem 1.1 (Posterior approval does not establish prior authorization).**

$$\exists A \in Bool \times Bool \to Bool,\; \exists R \in Bool \times Bool \to \left(Bool \to \left(Bool \to Prop\right)\right),\; \exists G \in Bool \times Bool \to Bool \times Bool,\; \exists x \in Bool \times Bool,\; A\left(G\left(x\right)\right) \ne A\left(x\right) \land \left(R\left(G\left(x\right)\right) \ne R\left(x\right) \land \left(\left(\neg modificationAuthorized\left(A, R, G, x\right)\right) \land \left(modificationAuthorized\left(A, R, G, G\left(x\right)\right) \land \left(\neg \left(modificationAuthorized\left(A, R, G, G\left(x\right)\right) \Rightarrow modificationAuthorized\left(A, R, G, x\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/PriorPosteriorAuthorizationSeparation.posterior_approval_authorization_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The authorization predicate evaluates the current approval standard on the action preference before and after the proposed change. It is constructed from those three source primitives.

The countermodel exposes its preference, approval standard, change, and original state as existential witnesses. The change flips both state components, so both revisions are part of the public statement.

The original approval bit rejects the preference transition. After the same process changes the subject, the new approval bit accepts the transition produced by applying that process again.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/PriorPosteriorAuthorizationSeparation.posterior_approval_authorization_separation`
