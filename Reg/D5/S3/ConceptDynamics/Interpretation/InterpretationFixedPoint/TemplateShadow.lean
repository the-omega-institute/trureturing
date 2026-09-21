import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena, theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points,
      statementIdentity := "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena, theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points,
      statementIdentity := "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open FourthFifthArenas
attribute [local instance] contextFintype contextDecidableEq
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.instDecidableIsBinaryFixedMeaningMkBoolProd in

register_information_theorem _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points in contextArena
  primitives contextRealization.toPrimitiveBundle realization context_bridge
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open FourthFifthArenas
attribute [local instance] contextFintype contextDecidableEq
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow.instDecidableIsBinaryFixedMeaningMkBoolProd
example : _root_.Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points.__information_unit.Statement =
    (FourthFifthRealizations.context_parameters_can_select_distinct_fixed_points_realization.toTheoremUnit
      context_parameters_can_select_distinct_fixed_points).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow
