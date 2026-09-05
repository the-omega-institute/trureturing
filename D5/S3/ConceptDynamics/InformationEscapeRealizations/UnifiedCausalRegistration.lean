/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Register the two faithful causal transitions on the unified arena. -/

import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration

open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment

local instance : DecidableEq IC.Model :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelDecidableEq

register_information_theorem observation_strictly_weaker_than_intervention
  in observationInterventionLawArena
  object_arena unifiedArena
  catalog unifiedCausal
  primitives observationInterventionUnifiedRealization.toPrimitiveBundle
  realization observation_intervention_unified_realization

register_information_theorem intervention_strictly_weaker_than_counterfactual
  in interventionCounterfactualLawArena
  object_arena unifiedArena
  catalog unifiedCausal
  primitives interventionCounterfactualUnifiedRealization.toPrimitiveBundle
  realization intervention_counterfactual_unified_realization

end D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration
