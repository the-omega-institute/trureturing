import Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion.finite_branching_path_clock_criterion]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
