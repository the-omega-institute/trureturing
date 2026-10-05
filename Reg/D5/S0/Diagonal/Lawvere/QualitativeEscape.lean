import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
import Reg.Support.ExistentialWitnessRegistrationTemplates



namespace Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
open ExistentialWitnessRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.Diagonal.EscapeCount
open _root_.D5.S0.Diagonal.Lawvere.QualitativeEscape



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Unit → Unit → Bool)) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w) true))) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.captured_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(capturedArena)⟩,
  objectArena := .law ⟨(capturedArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (capturedArena) (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedRealization) (capturedRealization.toPrimitiveBundle) ⟨(captured_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (captured_bridge) (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((capturedRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Unit → Unit → Bool)) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w) true)),
  variation := .evidence ⟨(captured_lawSensitive)⟩ (by first | exact (captured_lawSensitive) | exact ⟨_, _, (captured_lawSensitive)⟩),
  sensitivity := .evidence ⟨(captured_slotSensitive)⟩ (by exact (captured_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
open ExistentialWitnessRegistrationTemplates LeanInformationAudit
open _root_.D5.S0.Diagonal.EscapeCount
open _root_.D5.S0.Diagonal.Lawvere.QualitativeEscape
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.captured_bridge.toTheoremUnit _root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint).Statement =
    (∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g) := rfl
end

end Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape
