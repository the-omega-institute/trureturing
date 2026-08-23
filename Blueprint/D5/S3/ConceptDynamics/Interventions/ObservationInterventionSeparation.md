# Observation-Intervention Separation

## Abstract

Opposite Boolean causal directions can agree observationally while separating under intervention.

**Theorem 1.1 (Observation is strictly weaker than intervention).**

$$\exists M \in DeterministicBoolSCM, N \in DeterministicBoolSCM,\; Obs\left(M\right) = Obs\left(N\right) \land Int\left(M\right) \ne Int\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation.observation_strictly_weaker_than_intervention` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two witness models have opposite causal directions but use the identity as both their root and child mechanisms. For every exogenous input, each model therefore produces the same observed pair, so their observational maps coincide.

Fixing X to false separates the models when the exogenous input is true. The X-causes-Y model returns (false, false), whereas the Y-causes-X model returns (false, true). Their intervention maps are thus unequal despite observational equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation.observation_strictly_weaker_than_intervention`
