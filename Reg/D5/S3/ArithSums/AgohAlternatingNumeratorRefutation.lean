import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result) (type_of% (@coefficientRealization CoefficientCode
      (fun code index => actualCoefficientReadout code index))) (type_of% (actualCode)) (Unit) := {
  unitName := `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result.__information_unit,
  realizationName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.coefficient_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(coefficientArena)⟩,
  objectArena := .law ⟨(coefficientArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (coefficientArena) (D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.actualRealization) (actualRealization.toPrimitiveBundle) ⟨(coefficient_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (coefficient_bridge) (@_root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((actualRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@coefficientRealization CoefficientCode
      (fun code index => actualCoefficientReadout code index)),
  variation := .evidence ⟨(coefficient_variation)⟩ (by first | exact (coefficient_variation) | exact ⟨_, _, (coefficient_variation)⟩),
  sensitivity := .evidence ⟨(coefficient_sensitivity)⟩ (by exact (coefficient_sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (actualCode),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
