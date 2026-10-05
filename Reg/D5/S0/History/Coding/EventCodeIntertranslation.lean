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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 2) (Fin 2) (instDecidableEqFin 2) (fun i => i))) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.marker_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(markerArena)⟩,
  objectArena := .law ⟨(markerArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (markerArena) (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerRealization) (markerRealization.toPrimitiveBundle) ⟨(marker_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (marker_bridge) (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((markerRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 2) (Fin 2) (instDecidableEqFin 2) (fun i => i)),
  variation := .evidence ⟨(marker_lawSensitive)⟩ (by first | exact (marker_lawSensitive) | exact ⟨_, _, (marker_lawSensitive)⟩),
  sensitivity := .evidence ⟨(marker_slotSensitive)⟩ (by exact (marker_slotSensitive)),
  partialSensitivity := none,
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



noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 12) (Fin 12) (instDecidableEqFin 12) (fun i => i))) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcode_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(opcodeArena)⟩,
  objectArena := .law ⟨(opcodeArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (opcodeArena) (D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeRealization) (opcodeRealization.toPrimitiveBundle) ⟨(opcode_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (opcode_bridge) (@_root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((opcodeRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates.mapInjectiveRealization
    (Fin 12) (Fin 12) (instDecidableEqFin 12) (fun i => i)),
  variation := .evidence ⟨(opcode_lawSensitive)⟩ (by first | exact (opcode_lawSensitive) | exact ⟨_, _, (opcode_lawSensitive)⟩),
  sensitivity := .evidence ⟨(opcode_slotSensitive)⟩ (by exact (opcode_slotSensitive)),
  partialSensitivity := none,
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
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.marker_bridge.toTheoremUnit _root_.D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective).Statement =
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
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcode_bridge.toTheoremUnit _root_.D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective).Statement =
    Function.Injective opcodeIndex := rfl
end

end Reg.D5.S0.History.Coding.EventCodeIntertranslation
