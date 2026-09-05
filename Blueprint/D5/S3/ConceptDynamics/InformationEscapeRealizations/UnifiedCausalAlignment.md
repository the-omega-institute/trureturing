# Unified Causal Alignment

## Abstract

Two frozen Boolean causal separations align faithfully on one cumulative 48-state coproduct.

**Definition 1.1 (Unified causal arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical arena is the coproduct of the landed intervention-counterfactual and observation-intervention model carriers.

**Definition 1.2 (Unified observation-intervention signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedObservationInterventionSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedObservationInterventionSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two optional branch-local CUT readouts realize observation and intervention on the right coproduct branch.

**Definition 1.3 (Observation-intervention realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observationInterventionUnifiedRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observationInterventionUnifiedRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The OI readouts are injected faithfully while the opposite branch returns none.

**Definition 1.4 (Unified intervention-counterfactual signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedInterventionCounterfactualSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedInterventionCounterfactualSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two optional branch-local CUT readouts realize intervention and counterfactual information on the left branch.

**Definition 1.5 (Intervention-counterfactual realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.interventionCounterfactualUnifiedRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.interventionCounterfactualUnifiedRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The IC readouts are injected faithfully while the opposite branch returns none.

**Definition 1.6 (Cumulative observation readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.ObsU`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.ObsU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coarse readout combines one IC intervention slice with OI observation.

**Definition 1.7 (Cumulative intervention readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.IntU`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.IntU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The middle readout combines full IC intervention with paired OI observation and intervention.

**Definition 1.8 (Cumulative counterfactual readout).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.CfU`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.CfU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finest readout uses IC counterfactual tables and the literal OI model identity.

**Theorem 1.9 (Observation factors through intervention).**

$$ObsU = compose\left(obsFromInt, IntU\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.obsU_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each coproduct branch, forgetting intervention data computes exactly the cumulative observation readout.

**Theorem 1.10 (Intervention factors through counterfactual).**

$$IntU = compose\left(intFromCf, CfU\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.intU_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counterfactual collapse on the IC branch and direct restriction on the OI branch recover intervention data.

**Theorem 1.11 (Observation captures an explicit pair).**

$$inrX \neq inrDistinct \land ObsU\left(inrX\right) \neq ObsU\left(inrDistinct\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unified_observation_positive_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant-false OI model is off diagonal from the named X-causes-Y model and has a different observation readout.

**Theorem 1.12 (Intervention strictly refines observation).**

$$factorsKernel\left(IntU, ObsU\right) \land strictWitness\left(OI, IntU, ObsU\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unified_observation_intervention_strict_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization implication is paired with the injected opposite-direction OI witness.

**Theorem 1.13 (Counterfactual strictly refines intervention).**

$$factorsKernel\left(CfU, IntU\right) \land strictWitness\left(IC, CfU, IntU\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unified_intervention_counterfactual_strict_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization implication is paired with the injected IC no-effect and flip-effect witness.

**Definition 1.14 (Observation-intervention law arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observationInterventionLawArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observationInterventionLawArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The frozen OI law is interpreted only on the right branch of the shared arena.

**Definition 1.15 (Intervention-counterfactual law arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.interventionCounterfactualLawArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.interventionCounterfactualLawArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The frozen IC law is interpreted only on the left branch of the shared arena.

**Theorem 1.16 (Faithful OI transport).**

$$LegacyPrimitiveRealization\left(observationInterventionLawArena, OIStatement, observationInterventionUnifiedRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observation_intervention_unified_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward injection and reverse restriction both use their supplied equality and inequality witnesses.

**Theorem 1.17 (Faithful IC transport).**

$$LegacyPrimitiveRealization\left(interventionCounterfactualLawArena, ICStatement, interventionCounterfactualUnifiedRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.intervention_counterfactual_unified_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward injection and reverse restriction both use their supplied equality and inequality witnesses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.CfU`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.IntU`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.ObsU`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.intU_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.interventionCounterfactualLawArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.interventionCounterfactualUnifiedRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.intervention_counterfactual_unified_realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.obsU_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observationInterventionLawArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observationInterventionUnifiedRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.observation_intervention_unified_realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedInterventionCounterfactualSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unifiedObservationInterventionSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unified_intervention_counterfactual_strict_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unified_observation_intervention_strict_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment.unified_observation_positive_witness`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas](../InformationEscapeArenas/FourthFifthArenas.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/ObservationIntervention](../InformationEscapeArenas/ObservationIntervention.md)
- Dependency: [D5/S3/ConceptDynamics/Interventions/CounterfactualKernelStrictlyFiner](../Interventions/CounterfactualKernelStrictlyFiner.md)
