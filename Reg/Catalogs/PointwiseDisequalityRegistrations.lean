import Reg.D5.S0.Certificates.SkeletonChannelRetraction
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.PointwiseDisequalityRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      statementIdentity := "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      statementIdentity := "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      statementIdentity := "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      statementIdentity := "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  companionPrefix := some `Reg.Catalogs.PointwiseDisequalityRegistrations }

#seal_information_theory


section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S0.Certificates.SkeletonChannelRetraction].contains entry.registrationModuleName
  unless entries.size == 2 do throwError "relocated production occurrence count"
  for entry in entries do
    let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
    let some (.lit (.strVal diagnostic)) := info.value?
      | throwError "registration diagnostic is not a literal"
    if diagnostic.isEmpty then
      logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
    else
      logWarning diagnostic
end
