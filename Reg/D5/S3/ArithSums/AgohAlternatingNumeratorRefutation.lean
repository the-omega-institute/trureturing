import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
import Reg.Support.AgohCoefficientReadoutTemplate



namespace Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Polynomial Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.AgohCoefficientReadoutTemplate
open LeanInformationAudit
open _root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
attribute [local instance] _root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.instDecidableEqStateCoefficientArena in

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result) (type_of% (coefficientArena)) (type_of% (coefficientArena)) (type_of% (@coefficientRealization CoefficientCode
      (fun code index => actualCoefficientReadout code index))) (type_of% (coefficient_variation)) (type_of% (coefficient_sensitivity)) (type_of% (actualCode)) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result.__information_unit,
  realizationName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.coefficient_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(coefficientArena)⟩,
  objectArena := ⟨(coefficientArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (coefficientArena) (D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.actualRealization) (actualRealization.toPrimitiveBundle) ⟨(coefficient_bridge)⟩,
  readout := some (@coefficientRealization CoefficientCode
      (fun code index => actualCoefficientReadout code index)),
  variation := some ⟨(coefficient_variation)⟩,
  sensitivity := some ⟨(coefficient_sensitivity)⟩,
  escapeFrom := some (actualCode),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
