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

noncomputable def _root_.Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena (@Exists.{1} (Bool → Bool) fun (f : Bool → Bool) => @Exists.{1} (Unit → Unit → Bool) fun (g : Unit → Unit → Bool) => Not (@D5.S0.Diagonal.EscapeCount.IsEscaped.{0, 0} Unit Bool f g)) D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedRealization D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.captured_bridge D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint) (type_of% (capturedArena)) (type_of% (capturedArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Unit → Unit → Bool)) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w) true))) (type_of% (captured_lawSensitive)) (type_of% (captured_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.captured_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(capturedArena)⟩,
  objectArena := ⟨(capturedArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (capturedArena) (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedRealization) (capturedRealization.toPrimitiveBundle) ⟨(captured_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Unit → Unit → Bool)) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w) true)),
  variation := some ⟨(captured_lawSensitive)⟩,
  sensitivity := some ⟨(captured_slotSensitive)⟩,
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
example : _root_.Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint.__information_unit.Statement =
    (∃ (f : Bool → Bool) (g : Unit → Unit → Bool), ¬ IsEscaped f g) := rfl
end

end Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape
