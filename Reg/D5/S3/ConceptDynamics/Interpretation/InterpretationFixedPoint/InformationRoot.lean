import Reg.Support.LegacyContextReplacement
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
  expected := #[
    { objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points,
      statementIdentity := "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points,
      statementIdentity := "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot }


namespace Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open Reg.Support.LegacyContextReplacement
open LeanInformationAudit

register_information_theorem _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points
  in domainArena
  object_arena objectArena catalog Reg.Support.LegacyContextReplacement.objectArena
  readout via (cutRealization (fun x : ContextData => Reg.Support.LegacyContextCausalCodes.contextCode x))
  primitives actual.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.baselineContext) escape continues (open)

end Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
