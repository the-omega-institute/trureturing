# Observation Intervention Arena

## Abstract

Observation versus intervention is expressed by two typed CUT slots.

**Definition 1.1 (Causal-direction decidable equality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instDecidableEqCausalDirection`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instDecidableEqCausalDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decidable-equality instance is obtained by exhaustive constructor comparison.

**Definition 1.2 (Finite causal directions).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeCausalDirection`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeCausalDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite instance lists the two causal-direction constructors exhaustively.

**Definition 1.3 (Boolean SCM equivalence).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.scmEquiv`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.scmEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source models are equivalent to a direction paired with two unary Boolean tables.

**Definition 1.4 (Finite Boolean SCMs).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeDeterministicBoolSCM`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeDeterministicBoolSCM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite instance is obtained through a private equivalence.

**Definition 1.5 (Boolean SCM decidable equality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instDecidableEqDeterministicBoolSCM`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instDecidableEqDeterministicBoolSCM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decidable-equality instance is obtained through a private equivalence.

**Definition 1.6 (Observation readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.ObservationReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.ObservationReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout index type has one observational role and one interventional role.

**Definition 1.7 (Finite observation readouts).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeObservationReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeObservationReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite instance lists the two readout constructors exhaustively.

**Definition 1.8 (Observation-intervention signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature assigns typed Boolean response tables to two CUT readout indices.

**Definition 1.9 (Frozen observation-intervention statement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.ObservationInterventionStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.ObservationInterventionStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.

**Definition 1.10 (Observation-intervention arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law asks for two source models with equal observation CUTs and unequal intervention CUTs.

**Theorem 1.11 (Observation-intervention arena is nondegenerate).**

$$\operatorname{Nondegenerate}(\operatorname{toArena}(observationInterventionArena))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionArena_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite source carrier contains a pair of distinct models.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.ObservationInterventionStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.ObservationReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instDecidableEqCausalDirection`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instDecidableEqDeterministicBoolSCM`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeCausalDirection`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeDeterministicBoolSCM`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.instFintypeObservationReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionArena_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.observationInterventionSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention.scmEquiv`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
- Dependency: [D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation](../Interventions/ObservationInterventionSeparation.md)
