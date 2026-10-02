import LeanInformationAuditRegTests.ContractMapping
import Reg.ContractPrototype.Inline
import Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

/-- Reassess a current event and claim after changing only the arena expression.
The let-bound expression has the same value, constants, type and occurrence key. -/
private def changedArena (env : Environment) (record : BindingRecord) : MetaM (Environment × BindingRecord) := do
  let type ← inEnvironment env <| inferType record.occurrence.arena
  let arena := Expr.letE `arena type record.occurrence.arena (.bvar 0) false
  let event := { record.occurrence with arena }
  let claims := TemplateBinding.ownedClaims env
  let reset := (TemplateBinding.ownedEvents env).foldl
    (fun e (_, input) => TemplateBinding.addOccurrence e
      (if input.key == event.key then event else input))
    (TemplateBinding.resetAssessmentRecords env)
  let changed := claims.foldl (fun e (_, claim) => TemplateBinding.addClaim e
    (if claim.key == event.key then { claim with arena } else claim)) reset
  let some (_, claim) := (TemplateBinding.ownedClaims changed).find? (·.2.key == event.key)
    | throwError "arena_current_claim_missing"
  let fresh ← inEnvironment changed <| TemplateBinding.assess event (some claim)
  unless fresh.result matches .declaredValidated _ do throwError "arena_change_not_validated"
  unless !(event.arena.equal record.occurrence.arena) &&
      (← inEnvironment env <| isDefEq event.arena record.occurrence.arena) do
    throwError "arena_change_not_exercised"
  unless (← inEnvironment env <| TemplateBinding.recordJson record) ==
      (← inEnvironment changed <| TemplateBinding.recordJson fresh) do
    throwError "arena_change_modified_exported_record"
  verifyCurrentRecord "arena-control" changed fresh
  return (changed, fresh)

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let oldRoot := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
    let newRoot := `Reg.ContractPrototype.Inline
    let reports ← ContractPrototype.reports #[oldRoot, newRoot]
    let some (_, _, oldEnv) := reports[0]? | throwError "old_report_missing"
    let some (_, _, newEnv) := reports[1]? | throwError "new_report_missing"
    let record (env : Environment) (owner : Name) :=
      ((TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner))[0]!
    let oldRecord := record oldEnv oldRoot
    let newRecord := record newEnv newRoot
    let authorization := inlineAuthorization #[(oldRoot, newRoot),
      (`Reg.Support.BoundedRunSpace, `Reg.ContractPrototype.Templates.Cut)]
    discard <| verifyRecord oldEnv newEnv authorization oldRecord newRecord
    logInfo "[PASS] validated_equal_arena_control"
    let (changedOld, freshOld) ← changedArena oldEnv oldRecord
    discard <| rejected "validated_arena_old" "arena_mapping" <|
      verifyRecord changedOld newEnv authorization freshOld newRecord
    let (changedNew, freshNew) ← changedArena newEnv newRecord
    discard <| rejected "validated_arena_new" "arena_mapping" <|
      verifyRecord oldEnv changedNew authorization oldRecord freshNew
    setEnv saved
