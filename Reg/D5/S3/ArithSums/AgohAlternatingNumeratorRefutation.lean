import LeanInformationAudit.Syntax
import D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
import Reg.Support.AgohCoefficientReadoutTemplate

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
  expected := #[
    { objectArenaName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.coefficientArena, theoremName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result,
      statementIdentity := "sha256:b73243ac35b37e86857cc49f737e76604efcfd51d65dcf3d47ee5b444345ba32",
      registrationModuleName := `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation }]
  source := #[
    { objectArenaName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.coefficientArena, theoremName := `D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result,
      statementIdentity := "sha256:b73243ac35b37e86857cc49f737e76604efcfd51d65dcf3d47ee5b444345ba32",
      registrationModuleName := `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation }]
  companionPrefix := some `Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation }

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

register_information_theorem _root_.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation.result in coefficientArena
  readout via
    (@coefficientRealization CoefficientCode
      (fun code index => actualCoefficientReadout code index))
  primitives actualRealization.toPrimitiveBundle realization coefficient_bridge
  variation coefficient_variation sensitivity coefficient_sensitivity
  escape from (actualCode) escape continues (open)
end

end Reg.D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
