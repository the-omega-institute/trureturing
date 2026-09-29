import LeanInformationAudit.Syntax
import D5.S3.Arith.WuPyramidalComplement
import Reg.Support.WuPyramidalComplement

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.Arith.WuPyramidalComplement
  expected := #[
    { objectArenaName := `D5.S3.Arith.WuPyramidalComplement.branchArena, theoremName := `D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one,
      statementIdentity := "sha256:417e7452d5a85d1948edbffa69e9940cb47e8a6fb7c15c206b9fa65767ade842",
      registrationModuleName := `Reg.D5.S3.Arith.WuPyramidalComplement }]
  source := #[
    { objectArenaName := `D5.S3.Arith.WuPyramidalComplement.branchArena, theoremName := `D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one,
      statementIdentity := "sha256:417e7452d5a85d1948edbffa69e9940cb47e8a6fb7c15c206b9fa65767ade842",
      registrationModuleName := `Reg.D5.S3.Arith.WuPyramidalComplement }]
  companionPrefix := some `Reg.D5.S3.Arith.WuPyramidalComplement }

namespace Reg.D5.S3.Arith.WuPyramidalComplement

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.Arith.WuPyramidalComplement
attribute [local instance] _root_.D5.S3.Arith.WuPyramidalComplement.instDecidable_d5
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit

register_information_theorem _root_.D5.S3.Arith.WuPyramidalComplement.wu_conjecture_one in branchArena
  readout via
    (branchRealization (fun branch : Option Bool => branch))
  primitives (identityReadout).toPrimitiveBundle
  realization inline (identityReadout) := by exact ⟨Iff.rfl⟩
  variation branchVariation sensitivity branchSensitivity
  escape from (some true) escape continues (open)
end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.Arith.WuPyramidalComplement
attribute [local instance] _root_.D5.S3.Arith.WuPyramidalComplement.instDecidable_d5
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``wu_conjecture_one &&
      row.occurrence.key.registrationModule == env.header.mainModule)
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
