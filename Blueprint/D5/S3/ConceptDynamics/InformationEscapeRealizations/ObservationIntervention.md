# Observation Intervention Realization

## Abstract

The frozen observation-intervention theorem realizes a 24-class two-CUT kernel.

**Definition 1.1 (Concrete observation-intervention realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observationInterventionRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observationInterventionRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The primitive realization assigns the source observation and intervention functions to the two typed CUT slots.

**Theorem 1.2 (Observation-intervention realization).**

$${\exists M, N: DeterministicBoolSCM, Obs\left(M\right) = Obs\left(N\right) \land Int\left(M\right) \neq Int\left(N\right)} \iff observationInterventionArena.Law(observationInterventionRealization).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence preserves the existential model witnesses in both directions.

**Theorem 1.3 (Twenty-four kernel classes).**

$$(Finset.univ.image((model: DeterministicBoolSCM \mapsto (Obs\left(model\right), Int\left(model\right))))).card = 24.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhaustive evaluation of all 32 source models yields 24 joint signatures.

**Theorem 1.4 (Private pair separation).**

$$\neg observationInterventionRealization.toPrimitiveBundle.agrees(xCausesYModel, yCausesXModel).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named opposite-direction models disagree under intervention.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observationInterventionRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention](../InformationEscapeArenas/ObservationIntervention.md)
