import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
import LeanInformationAudit.Tests.RegistrationPersistence
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.ImportClosureProducer

-- The report host imports unrelated registration roots. Its mainModule must
-- neither widen the selected inventory nor become the generated proof owner.
run_cmd do
  let saved ← getEnv
  let root := `LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
  liftCoreM do
    assessAndSealRegistration (← RegistrationAssessmentInput.capture root)
  let env ← getEnv
  let records := SealRecords.forRoot env root
  unless records.size == 1 && records[0]!.catalog.rootId == root &&
      (SealRecords.forRoot env saved.header.mainModule).isEmpty do
    throwError "imported assessment changed root ownership"
  let row := records[0]!.theorems[0]!
  unless row.theoremName == ``importedTheorem && env.contains row.certificateName do
    throwError "imported assessment did not kernel-publish its selected proof"
  setEnv saved
  unless (SealRecords.forRoot (← getEnv) root).isEmpty do
    throwError "imported assessment could not restore the environment"

-- A snapshot cannot be replayed against a different environment.
run_cmd liftCoreM do
  let before ← getEnv
  let root := `LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
  let input ← RegistrationAssessmentInput.capture root
  addDecl <| .defnDecl {
    name := `unrelatedEnvironmentChange, levelParams := [],
    type := mkConst ``Nat, value := mkNatLit 1, hints := .abbrev, safety := .safe }
  let changed ← getEnv
  let rejected ← try
    assessAndSealRegistration input
    pure false
  catch error =>
    pure (((← error.toMessageData.toString).splitOn "rule=dtr.assessment_input").length == 2)
  unless rejected && (SealRecords.forRoot (← getEnv) root).isEmpty &&
      sameRegistrationEnvironment changed (← getEnv) do
    throwError "stale report input was accepted or changed the environment"
  setEnv before

-- A colliding row outside the selected root must not enter that root's catalog.
-- Mutating the real registry here exercises the lower validator as well as
-- the service's initial root selection.
run_cmd do
  let saved ← getEnv
  let some (name, _) := saved.constants.toList.find? (fun (name, _) =>
      privateToUserName name == `LeanInformationAudit.informationRegistryExt)
    | throwError "missing registry fixture extension"
  let extension := mkIdent name
  try
    elabCommand (← `(command| run_cmd do
      let root := `LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
      let some entry := (InformationRegistry.forRoot (← getEnv) root)[0]?
        | throwError "missing selected producer"
      let moved := { entry with registrationModuleName := `UnrelatedRegistration }
      modifyEnv fun env => ($extension).modifyState env fun state =>
        let entries := state.entries.push moved
        let theoremNames := state.theoremNames.insert moved.theoremName
        { state with entries, theoremNames }))
    let root := `LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
    liftCoreM do
      assessAndSealRegistration (← RegistrationAssessmentInput.capture root)
    unless (SealRecords.forRoot (← getEnv) root).size == 1 do
      throwError "unrelated collision entered the selected catalog"
    logInfo "[PASS] imported_root_ignores_unrelated_registry_collision"
  finally setEnv saved
