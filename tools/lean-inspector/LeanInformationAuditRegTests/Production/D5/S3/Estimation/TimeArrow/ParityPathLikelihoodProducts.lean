import Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product, `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product, `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
