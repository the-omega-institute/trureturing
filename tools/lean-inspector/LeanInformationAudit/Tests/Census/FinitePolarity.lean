import LeanInformationAudit.Tests.Census.Evidence

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit DispositionCensus

-- A kernel-valid proof of True cannot satisfy a positive occurrence certificate.
/-- info: finite-polarity rejected -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let root := `LeanInformationAudit.Tests.Census.Evidence
  let inventory := LeanInformationAudit.Tests.Census.Evidence.inventory
  liftTermElabM <| validateEvidence root inventory
  let some (registryName, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName? name == some `LeanInformationAudit.sealRecordExt)
    | throwError "private seal registry missing"
  let registryId := mkIdent registryName
  try
    elabCommand (← `(command| run_cmd
      modifyEnv fun current => ($registryId).modifyState current fun records =>
        records.map fun record => { record with theorems := record.theorems.map fun row =>
          { row with certificateName := ``True.intro } }))
    let rejected ← try
      liftTermElabM <| validateEvidence root inventory
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      pure (message.endsWith "invalid=seal_certificate.proposition")
    if rejected then logInfo "finite-polarity rejected"
    else logInfo "FAIL finite-polarity accepted unrelated certificate"
  finally setEnv env
