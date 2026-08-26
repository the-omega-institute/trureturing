# Injective Policy Coalition Threshold

## Abstract

A policy preserving every realized secret distinction has exactly the secret-recovery coalition threshold.

**Theorem 1.1 (Policy implementation and secret recovery have the same threshold).**

$$\forall I \in Type, X \in Type, V \in Type, B \in Type, U \in Type, decI \in \operatorname{DecidableEq}\left(I\right), share \in I \to \left(X \to V\right), secret \in X \to B, policy \in X \to U,\; \left(\exists j \in B \to U,\; policy = \operatorname{compose}\left(j, secret\right) \land \operatorname{InjOn}\left(j, \operatorname{range}\left(secret\right)\right)\right) \Rightarrow \operatorname{minimumCoalitionSize}\left({\Lambda K: \operatorname{Finset}\left(I\right), \operatorname{Refines}\left(policy, \operatorname{coalitionReadout}\left(share, K\right)\right)}\right) = \operatorname{minimumCoalitionSize}\left({\Lambda K: \operatorname{Finset}\left(I\right), \operatorname{Refines}\left(secret, \operatorname{coalitionReadout}\left(share, K\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/InjectivePolicyCoalitionThreshold.injective_policy_coalition_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coalition readouts, their attainable cardinality sets, and minimum size are imported from the frozen family rather than redeclared.

When the secret carrier is inhabited, an inverse on the realized secret image converts policy factorization back to secret factorization. When it is empty, the source state type is empty and both natural infima are zero.

No finite-participant instance or full-coalition recovery premise is needed; the equality holds for every finite coalition inside an arbitrary participant type.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/InjectivePolicyCoalitionThreshold.injective_policy_coalition_threshold`
- Dependency: [D5/S3/ConceptDynamics/InstitutionalCapture/KnowledgePolicyThreshold](KnowledgePolicyThreshold.md)
