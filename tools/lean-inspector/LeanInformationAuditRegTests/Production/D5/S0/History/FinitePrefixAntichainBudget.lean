import Reg.D5.S0.History.FinitePrefixAntichainBudget
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace Reg.D5.S0.History.FinitePrefixAntichainBudget
open Lean in
run_meta do
  let target := `D5.S0.History.FinitePrefixAntichainBudget.result
  let some record := (LeanInformationAudit.TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == target) | throwError "original occurrence absent"
  let .declaredValidated cert := record.result
    | throwError "registration failed: {(← LeanInformationAudit.TemplateBinding.recordJson record).compress}"
  unless record.escape.fromObject.isSome && record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "four slots incomplete"
  logInfo m!"declared_validated {cert.evidenceRef}"

end Reg.D5.S0.History.FinitePrefixAntichainBudget
