import Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

/-! The report's replay of the recorded inputs assesses the registrations of
`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy`;
the registration module itself only records them. -/

namespace Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
open Lean in
run_meta do
  for target in #[`D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_label_card,
      `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.periodic_grid_linear_statistics,
      `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_holonomy_constant,
      `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.edge_label_card,
      `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.anchored_vertex_card,
      `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.holonomy_sector_card,
      `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.exact_label_card,
      `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.seam_holonomy] do
    let some record := (LeanInformationAudit.TemplateBinding.records (← getEnv)).find? fun record =>
        record.occurrence.key.theoremName == target &&
          record.occurrence.key.registrationModule == `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
      | throwError "original occurrence absent: {target}"
    let .declaredValidated cert := record.result
      | throwError "registration failed: {(← LeanInformationAudit.TemplateBinding.recordJson record).compress}"
    logInfo m!"declared_validated {target} {cert.evidenceRef}"

end Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
