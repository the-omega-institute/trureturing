import Reg.D5.S3.Arith.WuPyramidalComplement
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

namespace Reg.D5.S3.Arith.WuPyramidalComplement
section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.Arith.WuPyramidalComplement
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
end
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.Arith.WuPyramidalComplement
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``wu_conjecture_one &&
      row.occurrence.key.registrationModule == `Reg.D5.S3.Arith.WuPyramidalComplement)
    | throwError "Wu registration evidence is missing"
  match row.result with
  | .declaredValidated _ =>
      unless row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "legacy" do
        throwError "Wu registration lacks a validated four-slot escape record"
  | .declaredUnresolved diagnostic =>
      throwError "Wu registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "Wu registration is undeclared"
end
end Reg.D5.S3.Arith.WuPyramidalComplement
