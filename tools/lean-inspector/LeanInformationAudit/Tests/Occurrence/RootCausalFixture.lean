import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

open Lean Lean.Elab.Command LeanInformationAudit
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment

namespace LeanInformationAudit.Tests.RootCausalFixture

instance : DecidableEq IC.Model :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelDecidableEq

theorem extraCausalTheorem :
    ∃ M N, Obs M = Obs N ∧
      D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int M ≠
        D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int N :=
  observation_strictly_weaker_than_intervention

/-- Simulate the content lane's registration module without adding D5 source. -/
def registerCausalFixture (second : Bool := true) (extra : Bool := false) :
    CommandElabM Unit := do
  let catalogId := mkIdent `«causal-unified-transitions»
  let originalModule := (← getEnv).header.mainModule
  modifyEnv (·.setMainModule
    `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration)
  try
    elabCommand (← `(command|
      register_information_theorem observation_strictly_weaker_than_intervention
        in observationInterventionLawArena
        object_arena unifiedArena
        catalog $catalogId
        primitives observationInterventionUnifiedRealization.toPrimitiveBundle
        realization observation_intervention_unified_realization))
    if second then
      elabCommand (← `(command|
        register_information_theorem intervention_strictly_weaker_than_counterfactual
          in interventionCounterfactualLawArena
          object_arena unifiedArena
          catalog $catalogId
          primitives interventionCounterfactualUnifiedRealization.toPrimitiveBundle
          realization intervention_counterfactual_unified_realization))
    if extra then
      elabCommand (← `(command|
        register_information_theorem extraCausalTheorem
          in observationInterventionLawArena
          object_arena unifiedArena
          catalog $catalogId
          primitives observationInterventionUnifiedRealization.toPrimitiveBundle
          realization observation_intervention_unified_realization))
  finally
    modifyEnv (·.setMainModule originalModule)

end LeanInformationAudit.Tests.RootCausalFixture
