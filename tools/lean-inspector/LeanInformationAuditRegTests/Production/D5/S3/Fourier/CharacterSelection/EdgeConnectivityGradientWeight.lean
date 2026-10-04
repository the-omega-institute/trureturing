import Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
