import Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

run_cmd do
  let expected : Array Lean.Name := #[`D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_gram, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_action, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.full_syndrome_decoder, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.gram_syndrome_encoder, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.positive_syndrome_encoder, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_action_on_encoding, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_mul, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_on_copy]
  let entries := (LeanInformationAudit.InformationRegistry.entries (← Lean.getEnv)).filter
    (·.registrationModuleName == `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel)
  unless entries.size == expected.size && expected.all (fun name =>
      entries.any (·.theoremName == name)) do
    throwError "assessed source occurrence inventory differs"
