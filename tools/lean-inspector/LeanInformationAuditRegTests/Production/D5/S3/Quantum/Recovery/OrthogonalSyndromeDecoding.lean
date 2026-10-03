import Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.decoding_syndrome_block, `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.orthogonal_syndrome_recovery, `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.syndrome_transport_orthogonal]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
