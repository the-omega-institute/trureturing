import Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.subcoordinateLaw_eq]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
