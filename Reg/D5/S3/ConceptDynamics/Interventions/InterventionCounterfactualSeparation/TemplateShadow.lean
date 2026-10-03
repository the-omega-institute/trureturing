import Reg.Support.LegacyCausalFinite
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
  expected := #[
    { objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyCausalCoordinates.icObjectArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
open _root_.Reg.Support.LegacyCausalFinite
open _root_.Reg.Support.LegacyCausalSlots (slotRealization)

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
  in _root_.Reg.Support.LegacyCausalSlots.localDomainArena
  object_arena Reg.Support.LegacyCausalCoordinates.icObjectArena catalog Reg.Support.LegacyCausalCoordinates.icObjectArena
  readout via (slotRealization (fun i x => localRead i x))
  primitives localActual.toPrimitiveBundle realization local_bridge
  variation local_variation sensitivity _root_.Reg.Support.LegacyCausalSlots.local_sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
