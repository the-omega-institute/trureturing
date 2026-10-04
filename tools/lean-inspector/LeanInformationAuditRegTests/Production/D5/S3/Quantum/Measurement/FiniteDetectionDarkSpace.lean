import Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.dark_space_eq_survival_defect_kernel]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
