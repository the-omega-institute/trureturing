import Reg.D5.S0.History.WellFoundedLeafMassConservation
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

/-! The report's replay of the recorded inputs assesses the registrations of
`Reg.D5.S0.History.WellFoundedLeafMassConservation`;
the registration module itself only records them. -/

namespace Reg.D5.S0.History.WellFoundedLeafMassConservation
open Lean in
run_meta do
  for target in #[`D5.S0.History.WellFoundedLeafMassConservation.result] do
    let some record := (LeanInformationAudit.TemplateBinding.records (← getEnv)).find? fun record =>
        record.occurrence.key.theoremName == target &&
          record.occurrence.key.registrationModule == `Reg.D5.S0.History.WellFoundedLeafMassConservation
      | throwError "original occurrence absent: {target}"
    let .declaredValidated cert := record.result
      | throwError "registration failed: {(← LeanInformationAudit.TemplateBinding.recordJson record).compress}"
    unless record.escape.fromObject.isSome && record.escape.bridgeKind == "source-equivalence" &&
        record.escape.continuation.any (·.kind == "open") do throwError "four slots incomplete: {target}"
    logInfo m!"declared_validated {target} {cert.evidenceRef}"

end Reg.D5.S0.History.WellFoundedLeafMassConservation
