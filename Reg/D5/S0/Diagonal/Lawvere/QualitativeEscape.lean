import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
import Reg.Support.ExistentialWitnessRegistrationTemplates

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint,
      statementIdentity := "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886",
      registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint,
      statementIdentity := "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886",
      registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape }]
  companionPrefix := some `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape }

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

register_information_theorem _root_.D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint in capturedArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Unit → Unit → Bool)) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedReadout w) true))
  primitives capturedRealization.toPrimitiveBundle realization captured_bridge
  variation captured_lawSensitive sensitivity captured_slotSensitive
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
