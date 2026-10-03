import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
import Reg.Support.MapInjectiveRegistrationTemplates



namespace Reg.D5.S0.History.Coding.EventCodeIntertranslation

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.History _root_.D5.S0.History.Coding.EventCodeIntertranslation

noncomputable def _root_.Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena (@Function.Injective.{1, 1} D5.S0.History.Marker Nat D5.S0.History.Coding.EventCodeIntertranslation.markerDigit) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerRealization D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.marker_bridge D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective) (type_of% (markerArena)) (type_of% (markerArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 2) (Fin 2) (instDecidableEqFin 2) (fun i => i))) (type_of% (marker_lawSensitive)) (type_of% (marker_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.marker_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(markerArena)⟩,
  objectArena := ⟨(markerArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (markerArena) (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerRealization) (markerRealization.toPrimitiveBundle) ⟨(marker_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 2) (Fin 2) (instDecidableEqFin 2) (fun i => i)),
  variation := some ⟨(marker_lawSensitive)⟩,
  sensitivity := some ⟨(marker_slotSensitive)⟩,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
open MapInjectiveRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.History _root_.D5.S0.History.Coding.EventCodeIntertranslation

noncomputable def _root_.Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena (@Function.Injective.{1, 1} D5.S0.History.Opcode Nat D5.S0.History.Coding.EventCodeIntertranslation.opcodeIndex) D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeRealization D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcode_bridge D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective) (type_of% (opcodeArena)) (type_of% (opcodeArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 12) (Fin 12) (instDecidableEqFin 12) (fun i => i))) (type_of% (opcode_lawSensitive)) (type_of% (opcode_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcode_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(opcodeArena)⟩,
  objectArena := ⟨(opcodeArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (opcodeArena) (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeRealization) (opcodeRealization.toPrimitiveBundle) ⟨(opcode_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 12) (Fin 12) (instDecidableEqFin 12) (fun i => i)),
  variation := some ⟨(opcode_lawSensitive)⟩,
  sensitivity := some ⟨(opcode_slotSensitive)⟩,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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
