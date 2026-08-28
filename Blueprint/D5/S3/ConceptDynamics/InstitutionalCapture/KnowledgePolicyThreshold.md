# Knowledge Policy Threshold

## Abstract

Secret recovery and injective secret policies have the same coalition-size threshold.

**Definition 1.1 (Coalition readout).**

Lean statement: `D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold.coalitionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold.coalitionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coalition readout exposes a participant's share exactly when its label belongs to the coalition, using none for absent labels.

**Theorem 1.2 (Knowledge and policy thresholds agree).**

$$\forall I, X, V, B, U: Type,\ [\operatorname{Fintype}(I)], [\operatorname{DecidableEq}(I)], [\operatorname{Nonempty}(B)],\ share: I \to \left(X \to V\right), secret: \operatorname{Concept}\left(X, B\right), policy: \operatorname{Concept}\left(X, U\right),\ policyFactor: {\exists policyMap: B \to U, policy = policyMap \circ secret \land \operatorname{InjOn}\left(policyMap, \operatorname{range}\left(secret\right)\right)},\ fullRecovery: \operatorname{Refines}\left(secret, \operatorname{coalitionReadout}\left(share, (univ: \operatorname{Finset}\left(I\right))\right)\right),\ \operatorname{minimumCoalitionSize}\left({\Lambda K: \operatorname{Finset}\left(I\right), \operatorname{Refines}\left(policy, \operatorname{coalitionReadout}\left(share, K\right)\right)}\right) = \operatorname{minimumCoalitionSize}\left({\Lambda K: \operatorname{Finset}\left(I\right), \operatorname{Refines}\left(secret, \operatorname{coalitionReadout}\left(share, K\right)\right)}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold.knowledge_policy_threshold_consistent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The secret and policy are readouts on the same state space. The policy factors through the secret by a map injective on the secret image, so its values preserve every secret distinction.

For each finite coalition, policy factorization is equivalent to secret factorization: the forward direction uses the inverse selected on the secret image, and the reverse direction composes the policy map.

Consequently the two sets of attainable coalition cardinalities are equal, and their natural infima, the source minimum thresholds, agree.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold.coalitionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold.knowledge_policy_threshold_consistent`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
