import Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let owned := LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)
  unless owned.size == 1 do throwError "expected one assessed measurement occurrence"
