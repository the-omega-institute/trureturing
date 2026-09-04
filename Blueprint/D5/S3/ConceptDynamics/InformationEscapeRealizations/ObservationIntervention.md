# Observation Intervention Realization

## Abstract

The frozen observation-intervention theorem realizes a 24-class two-CUT kernel.

**Theorem 1.1 (Observation-intervention realization).**

$$\operatorname{LegacyPrimitiveRealization}\left(observationInterventionArena, ObservationInterventionStatement, observationInterventionRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence preserves the existential model witnesses in both directions.

**Theorem 1.2 (Twenty-four kernel classes).**

$$\operatorname{card}\left(signatureClasses\right) = 24.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhaustive evaluation of all 32 source models yields 24 joint signatures.

**Theorem 1.3 (Private pair separation).**

$$\operatorname{Not}\left(\operatorname{agrees}\left(observationInterventionRealization, xCausesYModel, yCausesXModel\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named opposite-direction models disagree under intervention.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention.observation_strictly_weaker_than_intervention_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention](../InformationEscapeArenas/ObservationIntervention.md)
