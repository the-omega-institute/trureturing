import LeanInformationAuditRegTests.ContractMapping
import LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
import Reg.ContractPrototype.Witness
import Reg.D5.S3.Resource.VandermondeHyperbolicRefutation
import Reg.ContractPrototype.ValidWitness
import Reg.ContractPrototype.Controls.Witness

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

private def changedClaims (env : Environment) (record : BindingRecord)
    (descriptor : Option Expr) : Environment :=
  let claims := TemplateBinding.ownedClaims env
  let reset := (TemplateBinding.ownedEvents env).foldl
    (fun e (_, event) => TemplateBinding.addOccurrence e event)
    (TemplateBinding.resetAssessmentRecords env)
  claims.foldl (fun e (_, claim) => TemplateBinding.addClaim e
    (if claim.key == record.occurrence.key then { claim with descriptor } else claim)) reset

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let oldRoot := `Reg.D5.S3.Resource.VandermondeHyperbolicRefutation
    let newRoot := `Reg.ContractPrototype.Witness
    let missingOld := `Reg.ContractPrototype.Controls.Witness
    let missingNew := `Reg.ContractPrototype.ValidWitness
    let reports ← ContractPrototype.reports #[oldRoot, newRoot, missingOld, missingNew]
    let some (_, _, oldEnv) := reports[0]? | throwError "report_missing"
    let some (_, _, newEnv) := reports[1]? | throwError "report_missing"
    let record (env : Environment) (owner : Name) :=
      ((TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner))[0]!
    let oldRecord := record oldEnv oldRoot
    let newRecord := record newEnv newRoot
    let authorization : Authorization := {
      owners := #[(oldRoot, newRoot),
        (`Reg.Support.CounterexampleRecord, `Reg.ContractPrototype.Templates.Counterexample)] }
    discard <| ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv newEnv authorization oldRecord newRecord
    let changed := changedClaims newEnv newRecord none
    let claim := (TemplateBinding.ownedClaims changed).find? (·.2.key == newRecord.occurrence.key)
    let some (_, currentClaim) := claim | throwError "current_claim_missing"
    let current ← inEnvironment changed <| TemplateBinding.assess newRecord.occurrence (some currentClaim)
    unless current.descriptor.isNone do throwError "claim_change_not_exercised"
    let .declaredUnresolved currentDiagnostic := current.result | throwError "changed_current_state_not_unresolved"
    let .declaredUnresolved originalDiagnostic := newRecord.result | throwError "control_state_not_unresolved"
    unless currentDiagnostic != originalDiagnostic do throwError "no_current_diagnostic_difference"
    discard <| rejected "unresolved_current_descriptor" "new.current_descriptor" <|
      ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv changed authorization oldRecord newRecord
    discard <| rejected "unresolved_source_identity" "new.current_event_source" <|
      ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv newEnv authorization oldRecord
        { newRecord with occurrence := { newRecord.occurrence with registrationSourceIdentity := "stale-review-source" } }
    let removed := (TemplateBinding.ownedClaims newEnv).foldl (fun e (_, claim) =>
      if claim.key == newRecord.occurrence.key then e else TemplateBinding.addClaim e claim)
      ((TemplateBinding.ownedEvents newEnv).foldl (fun e (_, event) => TemplateBinding.addOccurrence e event)
        (TemplateBinding.resetAssessmentRecords newEnv))
    discard <| rejected "unresolved_current_claim_removed" "new.current_descriptor|new.current_binding_owner|new.current_result" <|
      ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv removed authorization oldRecord newRecord
    let escaped := (TemplateBinding.ownedClaims newEnv).foldl (fun e (_, claim) => TemplateBinding.addClaim e
      (if claim.key == newRecord.occurrence.key then
        { claim with escapeInput := { claim.escapeInput with openContinuation := false } } else claim))
      ((TemplateBinding.ownedEvents newEnv).foldl (fun e (_, event) => TemplateBinding.addOccurrence e event)
        (TemplateBinding.resetAssessmentRecords newEnv))
    let currentEscape ← inEnvironment escaped <| TemplateBinding.assess newRecord.occurrence
      (((TemplateBinding.ownedClaims escaped).find? (·.2.key == newRecord.occurrence.key)).map Prod.snd)
    unless currentEscape.escape != newRecord.escape do throwError "escape_change_not_exercised"
    discard <| rejected "unresolved_current_escape" "new.current_escape|new.current_result" <|
      ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv escaped authorization oldRecord newRecord
    let some (_, _, missingOldEnv) := reports[2]? | throwError "report_missing"
    let some (_, _, missingNewEnv) := reports[3]? | throwError "report_missing"
    let findMissing (env : Environment) (owner : Name) :=
      ((TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner)).find?
        (·.occurrence.key.theoremName == `Reg.ContractPrototype.Fixtures.Witness.third)
    let some oldMissing := findMissing missingOldEnv missingOld | throwError "old_missing"
    let some newMissing := findMissing missingNewEnv missingNew | throwError "new_missing"
    let missingAuthorization : Authorization := { owners := #[(missingOld, missingNew)] }
    discard <| verifyMissingRecord missingOldEnv missingNewEnv missingAuthorization oldMissing newMissing
    let events := TemplateBinding.ownedEvents missingNewEnv
    let replaced := events.foldl (fun e (_, event) => TemplateBinding.addOccurrence e event)
      (TemplateBinding.resetAssessmentRecords missingNewEnv)
    let claim : TemplateBindingClaim := {
      key := newMissing.occurrence.key, owner := missingNew, arena := newMissing.occurrence.arena
      descriptor := some (mkConst `Reg.ContractPrototype.Fixtures.Witness.reads) }
    let changedMissing := TemplateBinding.addClaim replaced claim
    let now ← inEnvironment changedMissing <| TemplateBinding.assess newMissing.occurrence (some claim)
    unless now.result matches .declaredUnresolved _ do throwError "new_claim_not_exercised"
    discard <| rejected "undeclared_current_claim" "new.current_descriptor|new.current_binding_owner|new.current_result" <|
      verifyMissingRecord missingOldEnv changedMissing missingAuthorization oldMissing newMissing
    setEnv saved
