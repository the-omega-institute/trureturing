import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration }

namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
local instance : DecidableEq IC.Model :=
  _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelDecidableEq

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
  in interventionCounterfactualLawArena
  object_arena unifiedArena
  catalog «causal-unified-transitions»
  primitives interventionCounterfactualUnifiedRealization.toPrimitiveBundle
  realization intervention_counterfactual_unified_realization
end

end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
