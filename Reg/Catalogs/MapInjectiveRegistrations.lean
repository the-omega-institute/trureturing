import Reg.D5.S0.History.Coding.EventCodeIntertranslation
import Reg.D5.S3.QuantumContext.ProjectionValuationObstruction
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.MapInjectiveRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective,
      statementIdentity := "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective,
      statementIdentity := "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective,
      statementIdentity := "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8",
      registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.markerArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.marker_digit_injective,
      statementIdentity := "sha256:a8a72984ee6e03fd422c616af7b7d089aa74da390c05f7710cbbbda1537b4e48",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.opcodeArena, theoremName := `D5.S0.History.Coding.EventCodeIntertranslation.opcode_index_injective,
      statementIdentity := "sha256:f6c867468f7db617eb31f910b6c94236158ff940a852c72020b35a0b813d1521",
      registrationModuleName := `Reg.D5.S0.History.Coding.EventCodeIntertranslation },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations.rayArena, theoremName := `D5.S3.QuantumContext.ProjectionValuationObstruction.ks_vectors_injective,
      statementIdentity := "sha256:f03e68530cb8bea7d2c635a151ac9a19cafa007d9c4b3c8919636eac11b477f8",
      registrationModuleName := `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction }]
  companionPrefix := some `Reg.Catalogs.MapInjectiveRegistrations }

set_option maxRecDepth 100000 in
#seal_information_theory


section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S0.History.Coding.EventCodeIntertranslation, `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction].contains entry.registrationModuleName
  unless entries.size == 3 do throwError "relocated production occurrence count"
  for entry in entries do
    let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
    let some (.lit (.strVal diagnostic)) := info.value?
      | throwError "registration diagnostic is not a literal"
    if diagnostic.isEmpty then
      logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0]]"
    else
      logWarning diagnostic
end
