import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
import Reg.Support.MapInjectiveRegistrationTemplates

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S0.History.Coding.EventCodeIntertranslation
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective,
      statementIdentity := "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective,
      statementIdentity := "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective,
      statementIdentity := "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective,
      statementIdentity := "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation }]
  companionPrefix := some `Reg.D5.S0.History.Coding.EventCodeIntertranslation }

namespace Reg.D5.S0.History.Coding.EventCodeIntertranslation

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.History _root_.D5.S0.History.Coding.EventCodeIntertranslation

register_information_theorem _root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective in markerArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 2) (Fin 2) (instDecidableEqFin 2) (fun i => i))
  primitives markerRealization.toPrimitiveBundle realization marker_bridge
  variation marker_lawSensitive sensitivity marker_slotSensitive
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.History _root_.D5.S0.History.Coding.EventCodeIntertranslation

register_information_theorem _root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective in opcodeArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 12) (Fin 12) (instDecidableEqFin 12) (fun i => i))
  primitives opcodeRealization.toPrimitiveBundle realization opcode_bridge
  variation opcode_lawSensitive sensitivity opcode_slotSensitive
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.History _root_.D5.S0.History.Coding.EventCodeIntertranslation
example : _root_.Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective.__information_unit.Statement =
    Function.Injective markerDigit := rfl
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.History _root_.D5.S0.History.Coding.EventCodeIntertranslation
example : _root_.Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective.__information_unit.Statement =
    Function.Injective opcodeIndex := rfl
end

end Reg.D5.S0.History.Coding.EventCodeIntertranslation
