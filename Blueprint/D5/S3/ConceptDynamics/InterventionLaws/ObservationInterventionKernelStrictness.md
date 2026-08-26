# Observation-Intervention Kernel Strictness

## Abstract

The intervention kernel is already strictly finer than the observational kernel on finite Boolean structural models.

**Theorem 1.1 (The first causal-kernel inclusion is strict).**

$$\begin{gathered}IntProfile : DeterministicBoolSCM \to \left(Option\left(Bool\right) \to \left(Bool \to Bool \times Bool\right)\right),\\{}IntProfile(M, a, u) := optionCases\left(a, Obs\left(M, u\right), \lambda x, Int\left(M, x, u\right)\right),\\{}StrictSubset\left(ker\left(IntProfile\right), ker\left(Obs\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The intervention profile is constructed from the frozen finite Boolean structural-model channels. Its null action is exactly the observational response, while each nonnull action imposes one Boolean X value.

Equality of complete intervention profiles therefore forces observational equality by evaluation at the null action.

The frozen opposite-direction models have the same observational response but distinct imposed-X responses. Their pair belongs to the observational kernel and not the intervention kernel, making the inclusion strict.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation`
- Dependency: [D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation](../Interventions/ObservationInterventionSeparation.md)
