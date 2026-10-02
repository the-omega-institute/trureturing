import Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

/-! The report's replay of the recorded inputs assesses the registrations of
`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift`;
the registration module itself only records them. -/

namespace Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
open Lean in
run_meta do
  for target in #[`D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.flat_unique_cover_lift] do
    let some record := (LeanInformationAudit.TemplateBinding.records (← getEnv)).find? fun record =>
        record.occurrence.key.theoremName == target &&
          record.occurrence.key.registrationModule == `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
      | throwError "original occurrence absent: {target}"
    let .declaredValidated cert := record.result
      | throwError "registration failed: {(← LeanInformationAudit.TemplateBinding.recordJson record).compress}"
    logInfo m!"declared_validated {target} {cert.evidenceRef}"

end Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
