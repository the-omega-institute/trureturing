import LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration
import LeanInformationAudit.Census.Stream

open Lean LeanInformationAudit LeanInformationAudit.TemplateBinding Lean.Elab.Command

-- Existing independently compiled source and registration exercise the raw olean reader.
run_cmd do
  let env ← getEnv
  let source := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSource
  let producer := `LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration
  let theoremName := `LeanInformationAudit.Tests.DeclaredSource.original
  for owner in #[source, producer] do
    let some index := env.getModuleIdx? owner
      | throwError "[FAIL] existing_origin_fixture_missing"
    let rows := CensusStream.registryRecords owner.toString env.header.moduleData[index.toNat]!
    let bindings ← ofExcept <| rows.getObjValAs? (Array Json) "bindings"
    let matching := bindings.filter fun row =>
      (row.getObjVal? "key").toOption == some (nameJson theoremName)
    unless matching.size == (if owner == source then 0 else 2) do throwError "[FAIL] native_binding_origin_count"
    unless matching.all (fun row =>
        (row.getObjValAs? String "module").toOption == some owner.toString) do
      throwError "[FAIL] native_binding_origin_label"
  logInfo "[PASS] native_binding_origin_count native_binding_origin_label"

run_cmd do
  let env ← getEnv
  let producer := `LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration
  unless (ownedRecords env).map (·.1) == #[producer] do
    throwError "[FAIL] binding_record_producer_order"
  let joined ← ofExcept <| cachedJoinedRecords env
  unless joined.size == 1 && joined[0]!.bindingOwner == some producer &&
      (joined[0]!.result matches .declaredValidated _) do
    throwError "[FAIL] cached_producer_join"
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName name == `LeanInformationAudit.TemplateBinding.bindingRecords)
    | throwError "[FAIL] missing_binding_record_store"
  unless (env.getModuleIdxFor? name).map (env.allImportedModuleNames[·.toNat]!) ==
      some `LeanInformationAuditInterface.Store do
    throwError "[FAIL] binding_record_store_owner"
  -- Access the real extension only inside this fixture, to test the existing
  -- imported-container check without creating a second store or public mutator.
  let extension := mkIdent name
  try
    elabCommand (← `(command| run_cmd do
      modifyEnv fun current => ($extension).toEnvExtension.modifyState current fun state =>
        { state with importedEntries := state.importedEntries.map fun rows => rows.map fun row =>
          if row.bindingOwner.isSome then { row with bindingOwner := some `wrongOwner } else row }))
    match cachedJoinedRecords (← getEnv) with
    | .error "incomplete_closure:dtr.cached_record_owner" => pure ()
    | _ => throwError "[FAIL] cached_imported_owner_diagnostic"
  finally setEnv env
  logInfo "[PASS] binding_record_producer_order cached_producer_join \
    binding_record_store_owner cached_imported_owner_rejected"

private def rejectCachedRecord (change : TSyntax `term) (diagnostic : String) :
    CommandElabM Unit := do
  let env ← getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName name == `LeanInformationAudit.TemplateBinding.bindingRecords)
    | throwError "missing binding record store"
  let extension := mkIdent name
  try
    elabCommand (← `(command| run_cmd do
      modifyEnv fun current => ($extension).modifyState current fun rows => rows.map fun row =>
        if row.bindingOwner.isSome then ($change) row else row))
    match cachedJoinedRecords (← getEnv) with
    | .error reason => unless reason == diagnostic do throwError "[FAIL] {reason} != {diagnostic}"
    | .ok _ => throwError "[FAIL] cached_record_mutation_accepted"
    -- Authoritative assessment joins occurrences and claims, independently of
    -- these transported result payloads.
    let assessed ← liftTermElabM assessJoined
    unless assessed.size == 1 && (assessed[0]!.result matches .declaredValidated _) do
      throwError "[FAIL] transported_result_changed_assessment"
  finally setEnv env
  logInfo m!"[PASS] {diagnostic} authoritative_assessment_independent_of_stored_result"

run_cmd do
  rejectCachedRecord (← `(term| fun row => { row with occurrence :=
    { row.occurrence with statementIdentity := "changed" } }))
    "incomplete_closure:dtr.cached_record_inputs"
  rejectCachedRecord (← `(term| fun row => { row with descriptor := none }))
    "incomplete_closure:dtr.cached_descriptor"
  rejectCachedRecord (← `(term| fun row => { row with result := .undeclared }))
    "incomplete_closure:dtr.cached_declared"
  rejectCachedRecord (← `(term| fun row => { row with result := match row.result with
    | .declaredValidated certificate => .declaredValidated { certificate with
        key := { certificate.key with theoremName := `wrongTheorem } }
    | result => result })) "incomplete_closure:dtr.cached_certificate"
  let env ← getEnv
  let joined ← ofExcept <| cachedJoinedRecords env
  match cachedJoinedRecords (addRecord env joined[0]!) with
  | .error "incomplete_closure:dtr.cached_record_missing" =>
    logInfo "[PASS] cached_duplicate_record_rejected"
  | _ => throwError "[FAIL] cached_duplicate_record_accepted"
