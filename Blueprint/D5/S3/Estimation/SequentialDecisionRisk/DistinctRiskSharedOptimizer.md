# Distinct Risks with a Shared Optimizer

## Abstract

Distinct expected-risk profiles can induce the same complete optimizer profile.

**Theorem 1.1 (Different risk values can have the same argmin profile).**

$$\exists Psi \in Bool \to \operatorname{PMF}\left(Bool\right), ell \in Unit \to \left(Bool \to \left(Bool \to \mathbb{R}\right)\right),\; \operatorname{riskProfile}\left(Psi, ell, false\right) \ne \operatorname{riskProfile}\left(Psi, ell, true\right) \land \operatorname{optimizerProfile}\left(Psi, ell, false\right) = \operatorname{optimizerProfile}\left(Psi, ell, true\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/DistinctRiskSharedOptimizer.distinct_risk_profiles_can_share_optimizer_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Boolean history is mapped to the matching pure Boolean outcome law. The loss depends on the outcome but not on the action, using the canonical finite-sum riskProfile from the imported hierarchy.

The two histories therefore have different risk profiles, while every action ties at each history. Their canonical optimizerProfile values are equal, giving the required reverse-inclusion countermodel.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/DistinctRiskSharedOptimizer.distinct_risk_profiles_can_share_optimizer_profile`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/PredictiveRiskOptimizerHierarchy](PredictiveRiskOptimizerHierarchy.md)
