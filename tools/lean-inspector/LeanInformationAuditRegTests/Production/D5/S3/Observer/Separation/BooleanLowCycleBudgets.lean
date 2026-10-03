import Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets
open _root_.D5.S3.Observer.Separation.BooleanLowCycleBudgets
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let rows := (TemplateBinding.records env).filter fun row =>
    row.occurrence.key.theoremName ==
      `D5.S3.Observer.Separation.BooleanLowCycleBudgets.result &&
    row.occurrence.key.registrationModule == `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets
  unless rows.size == 1 do throwError "expected exactly one source-owner registration"
  let row := rows[0]!
  match row.result with
  | .declaredValidated certificate =>
      unless certificate.sourceBinding.isSome && row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "source-equivalence" do
        throwError "incomplete four-slot source-equivalence evidence"
  | .declaredUnresolved diagnostic => throwError "registration unresolved: {diagnostic}"
  | .undeclared => throwError "registration undeclared"
  logInfo m!"REG_BINDING_EVIDENCE {(← TemplateBinding.recordJson row).compress}"

end Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets
