import Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
