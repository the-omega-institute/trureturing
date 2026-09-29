import LeanInformationAudit.Tests.RegistrationErrors

open Lean

set_option linter.style.longLine false

namespace LeanInformationAudit.Tests.RegistrationPersistence

/-- info: 3 -/
#guard_msgs in
run_cmd do
  let entries := InformationRegistry.entries (← getEnv)
  logInfo m!"{entries.size}"

#guard_msgs in
run_cmd do
  let env ← getEnv
  unless InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.RegistrationErrors.nativeExample do
    throwError "missing persisted native registration"
  unless InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample do
    throwError "missing persisted legacy registration"
  unless InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample do
    throwError "missing persisted imported registration"
  let some legacyEntry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample
    | throwError "legacy registration lookup failed"
  unless legacyEntry.unitName ==
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample.__information_unit do
    throwError "legacy registration lookup returned the wrong unit"
  let some importedEntry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample
    | throwError "imported registration lookup failed"
  let importedUnitName :=
    `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample
      |>.str "__information_unit"
  unless importedEntry.unitName == importedUnitName do
    throwError "imported registration lookup returned the wrong unit"
  unless env.contains importedEntry.unitName do
    throwError "resolved companion declaration is missing"

#guard_msgs in
run_cmd do
  let env ← getEnv
  let some entry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.RegistrationErrors.nativeExample
    | throwError "missing persisted native registration"
  match ← Lean.Elab.Command.liftTermElabM <| validatePersistedEntry env.header.mainModule env entry with
  | .ok () => pure ()
  | .error message => throwError message

/-- error: IE-C002 DuplicateRegistration object_arena=LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena theorem_name=LeanInformationAudit.Tests.RegistrationErrors.legacyExample registration_modules=["LeanInformationAudit.Tests.RegistrationErrors","LeanInformationAudit.Tests.RegistrationPersistence"] count=2 -/
#guard_msgs (error) in
register_information_theorem
  LeanInformationAudit.Tests.RegistrationErrors.legacyExample
  in LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
  primitives LeanInformationAudit.Tests.RegistrationErrors.fixtureBundle
  realization LeanInformationAudit.Tests.RegistrationErrors.legacyRealization

private def indexException (action : Lean.Elab.Command.CommandElabM Unit) :
    Lean.Elab.Command.CommandElabM (Option Exception) :=
  fun context state => do
    try action context state; return none
    catch error => return some error

/-- Compare the derived membership view to the authoritative ordered rows,
including negative probes and generated companion names. -/
private def checkIndex (env : Environment) (extra : Array Name := #[]) :
    Lean.Elab.Command.CommandElabM Unit := do
  let entries := InformationRegistry.entries env
  let probes := extra ++ #[Name.anonymous, `RegistryIndexMissing] ++
    entries.flatMap (fun row => #[row.theoremName, row.unitName, row.realizationName])
  for row in entries do
    unless InformationRegistry.hasOccurrence env row.canonicalObjectArenaName row.theoremName do
      throwError "ordered occurrence disappeared from lookup"
  for name in probes do
    unless InformationRegistry.hasTheorem env name ==
        entries.any (fun row => row.theoremName == name) do
      throwError "registry membership differs from ordered scan: {name}"

local instance : DecidableEq RegistrationErrors.fixtureLawArena.State :=
  RegistrationErrors.fixtureLawArena.toArena.stateDecidableEq

/-- info: [PASS] registry_index_import_insert_duplicate_rollback_order -/
#guard_msgs in
run_cmd do
  let initial ← get
  let imported := InformationRegistry.entries initial.env
  unless imported.map (·.theoremName) == #[
      `LeanInformationAudit.Tests.RegistrationErrors.nativeExample,
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample,
      `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample] do
    throwError "persistent import changed entry or occurrence order"
  checkIndex initial.env
  let name := initial.env.header.mainModule.str "indexInserted"
  let target := Lean.mkIdent (`_root_ ++ name)
  let staged ← IO.mkRef false
  let caught ← indexException <|
    LeanInformationAudit.registrationTransaction do
      Lean.Elab.Command.elabCommand (← `(command|
        information_theorem $target
          in LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
          primitives LeanInformationAudit.Tests.RegistrationErrors.fixtureRealization
          : LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena.Law
              LeanInformationAudit.Tests.RegistrationErrors.fixtureRealization := by trivial))
      let env ← getEnv
      let rows := InformationRegistry.entries env
      checkIndex env #[name]
      let some inserted := rows.back? | throwError "insertion produced no entry"
      unless rows.size == imported.size + 1 && inserted.theoremName == name do
        throwError "insertion did not append one occurrence"
      unless (rows.extract 0 imported.size).zip imported |>.all
          (fun (a, b) => sameEntry a b) do
        throwError "insertion changed imported entry order or identities"
      let beforeDuplicate ← getEnv
      let duplicate ← indexException do
        discard <| registerSemanticEntry (← getEnv).header.mainModule inserted
      let some error := duplicate | throwError "duplicate occurrence was accepted"
      unless (← error.toMessageData.toString).startsWith "IE-C002 DuplicateRegistration" do
        throwError "duplicate occurrence changed its first rejection"
      let afterDuplicate ← getEnv
      checkIndex afterDuplicate #[name]
      let previous := InformationRegistry.entries beforeDuplicate
      let current := InformationRegistry.entries afterDuplicate
      unless previous.size == current.size &&
          (previous.zip current).all (fun (a, b) => sameEntry a b) do
        throwError "duplicate attempt changed entries or occurrence order"
      staged.set true
      throwError "registry index rollback injection"
  unless caught.isSome && (← staged.get) do
    throwError "insertion/duplicate assertions were not reached"
  let restored ← getEnv
  checkIndex restored #[name]
  let rows := InformationRegistry.entries restored
  unless !InformationRegistry.hasTheorem restored name && rows.size == imported.size &&
      (rows.zip imported).all (fun (a, b) => sameEntry a b) do
    throwError "rollback changed membership, occurrence order or identities"
  set initial
  logInfo "[PASS] registry_index_import_insert_duplicate_rollback_order"

end LeanInformationAudit.Tests.RegistrationPersistence

-- The prefix fast path must preserve the complete old predicate, including
-- anonymous/numeric names, arbitrary parents and every reserved suffix.
example (name : Lean.Name) : LeanInformationAudit.isCompanionName name =
    (match name with
     | .str _ suffix => LeanInformationAudit.generatedCompanionSuffixes.contains suffix
     | _ => false) := by
  cases name with
  | anonymous => rfl
  | num _ _ => rfl
  | str parent suffix =>
    simp only [LeanInformationAudit.isCompanionName]
    cases h : LeanInformationAudit.generatedCompanionSuffixes.contains suffix with
    | false => simp
    | true =>
      have hm : suffix ∈ LeanInformationAudit.generatedCompanionSuffixes :=
        Array.mem_of_contains_eq_true h
      simp [LeanInformationAudit.generatedCompanionSuffixes,
        LeanInformationAudit.theoremUnitSuffix, LeanInformationAudit.primitiveRealizationSuffix] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> subst suffix <;>
        simp only [Bool.and_true, String.startsWith_string_iff] <;> decide
