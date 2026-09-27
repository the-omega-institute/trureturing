import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import Reg.Support.PointwiseEqualityRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S0.Tower.DBonacci.Substitution
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible,
      statementIdentity := "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0",
      registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible,
      statementIdentity := "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0",
      registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution }]
  companionPrefix := some `Reg.D5.S0.Tower.DBonacci.Substitution }

namespace Reg.D5.S0.Tower.DBonacci.Substitution

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Tower.DBonacci.Substitution
open _root_.D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)

register_information_theorem _root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible in substitutionArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun label => label) (fun label => label))
  primitives substitutionRealization.toPrimitiveBundle realization substitution_bridge
  variation substitution_lawSensitive sensitivity substitution_slotSensitive
  escape from (Fin 3) escape continues (substitution_empty)
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Tower.DBonacci.Substitution
open _root_.D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)
example : _root_.Reg.D5.S0.Tower.DBonacci.Substitution.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible.__information_unit.Statement =
    (∀ label : Fin 3, (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
      gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) := rfl
end

end Reg.D5.S0.Tower.DBonacci.Substitution
