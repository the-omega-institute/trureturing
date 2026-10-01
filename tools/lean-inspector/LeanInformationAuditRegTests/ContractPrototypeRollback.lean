import LeanInformationAudit.ContractPrototype.Replay
import Reg.ContractPrototype.IffCatalog
import Reg.ContractPrototype.Readout

open Lean Meta Elab Command LeanInformationAudit

private def stateImage (env : Environment) (snapshot : ContractPrototype.Snapshot) : MetaM Json := do
  let roots := (RootCatalogs.owned env).map fun (owner, row) =>
    (owner.toString, reprStr row.expected, reprStr row.source, reprStr row.baseline,
      row.companionPrefix.map Name.toString)
  let plans := snapshot.enrollments.map fun (_, input) =>
    match TemplateAudit.selectedPlan env input.name with
    | .error reason => (input.name.toString, reason)
    | .ok plan => (input.name.toString, match TemplateAudit.planEncodingWithWork plan with
      | .error reason => reason
      | .ok (bytes, work) => s!"{Sha256.hex bytes}/{bytes.size}/{work}")
  let records ← (TemplateBinding.records env).mapM TemplateBinding.recordJson
  let companions := GeneratedDeclarations.entries env
  let declarations := companions.map fun (name, _) =>
    (name.toString, (env.find? name).map fun (info : ConstantInfo) =>
      (info.levelParams.map Name.toString, reprStr info.type, reprStr (info.value? true)))
  return Json.mkObj [
    ("roots", toJson roots), ("expectations", toJson (reprStr (ExpectedOccurrenceManifest.owned env))),
    ("companions", toJson (companions.map fun (a,b) => (a.toString,b.toString))),
    ("declarations", toJson declarations), ("plans", toJson plans),
    ("plan_bytes", toJson (TemplateAudit.assessedPlanBytes env)),
    ("records", toJson records), ("registry", toJson ((InformationRegistry.entries env).map fun row =>
      (row.theoremName.toString, row.unitName.toString, row.realizationName.toString,
        row.registrationModuleName.toString, row.canonicalObjectArenaName.toString))),
    ("seals", toJson (← serializeSealArtifact (SealRecords.entries env)))]

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let root := `Reg.ContractPrototype.IffCatalog
    let followup := `Reg.ContractPrototype.Readout
    let snapshot ← ContractPrototype.discover #[root, followup]
    let some (_, contract) := snapshot.roots.find? (·.1 == root)
      | throwError "rollback_root_control_missing"
    let row := contract.expected[0]!
    let snapshot := { snapshot with expected := snapshot.expected ++ #[(root, {
      rootId := root, objectArenaName := row.objectArenaName, theoremName := row.theoremName,
      statementIdentity := row.statementIdentity, capturedStatement := row.capturedStatement,
      registrationModuleName := row.registrationModuleName })] }
    let before ← stateImage saved snapshot
    ContractPrototype.replay followup snapshot
    unless (TemplateBinding.records (← getEnv)).any (fun record =>
        record.occurrence.key.registrationModule == followup &&
          match record.result with | .declaredValidated _ => true | _ => false) do
      throwError "rollback_followup_control_not_validated"
    let clean ← stateImage (← getEnv) snapshot
    unless clean != before do throwError "rollback_control_did_not_write"
    for stage in #["root", "expectation", "companions", "reset", "assessment", "seal"] do
      withCurrHeartbeats do
        setEnv saved
        let injected : Exception := .error Syntax.missing <|
          .tagged `runtime.maxHeartbeats m!"contract_resource_injection:{stage}"
        unless injected.isRuntime do throwError "injection_is_not_runtime"
        let reached ← IO.mkRef false
        let caught ← tryCatchRuntimeEx (do
          ContractPrototype.replay root snapshot fun current => do
            if current == stage then
              unless (← stateImage (← getEnv) snapshot) != before do
                throwError "injection_before_environment_write:{stage}"
              reached.set true
              throw injected
          pure none) (fun error => pure (some error))
        let some error := caught | throwError "resource_exception_was_swallowed:{stage}"
        unless (← reached.get) && error.isMaxHeartbeat &&
            (← error.toMessageData.toString) == (← injected.toMessageData.toString) do
          throwError "resource_exception_was_rewritten:{stage}"
        unless (← stateImage (← getEnv) snapshot) == before do
          throwError "[FAIL] runtime_replay_restores_all_state:{stage}"
        for (_, payload) in snapshot.companions do
          for name in #[payload.input.entry.unitName, payload.input.entry.realizationName] do
            unless ((← getEnv).find? name).isSome == (saved.find? name).isSome do
              throwError "runtime_replay_leaked_companion:{stage}:{name}"
        ContractPrototype.replay followup snapshot
        unless (← stateImage (← getEnv) snapshot) == clean do
          throwError "runtime_replay_followup_matches_clean:{stage}"
        logInfo m!"[PASS] runtime_replay_restores_all_state:{stage} followup_matches_clean=true"
    setEnv saved
