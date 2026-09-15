import LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecar
import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected

namespace LeanInformationAudit.Tests.DeclaredAssessmentCache
open Lean Meta Elab Command TemplateBinding TemplateAudit

private def observe (name : String) (ok : Bool) : MetaM Unit :=
  logInfo m!"[{if ok then "PASS" else "FAIL"}] {name}"

run_meta do
  let initial ← getEnv
  let rows ← assessJoined
  let #[record] := rows | throwError "setup: exactly one sidecar occurrence required"
  let .declaredValidated _ := record.result | throwError "setup: sidecar is not validated"
  let some descriptor := record.descriptor | throwError "setup: descriptor absent"
  let some owner := record.bindingOwner | throwError "setup: binding owner absent"
  let .ok plan := selectedPlan (← getEnv) descriptor.getAppFn.constName!
    | throwError "setup: selected plan absent"
  let primed ← getEnv
  let before := (observedAssessments primed).size
  discard <| assessJoined
  observe "authoritative_assessment_reused" ((observedAssessments (← getEnv)).size == before)
  setEnv primed
  let path := TemplateAudit.sourcePath plan.enrollmentOwner
  let original ← IO.FS.readBinFile path
  try
    IO.FS.writeFile path ((String.fromUTF8! original) ++ "\n-- changed selected enrollment input\n")
    let changed ← assessJoined
    let rejected := changed.all fun row => match row.result with
      | .declaredUnresolved diagnostic => (diagnostic.splitOn "E7.stale_source").length > 1
      | _ => false
    observe "changed_template_invalidates_users" rejected
  finally IO.FS.writeBinFile path original
  setEnv primed
  -- An isolated change to the retained statement identity must not reuse the old
  -- record. Native ownership/statement validation is separately tested at the join.
  let changed := { record.occurrence with statementIdentity := "changed-statement-identity" }
  let claim : TemplateBindingClaim := {
    key := changed.key, arena := changed.arena, descriptor := some descriptor, owner }
  let revised ← assess changed (some claim)
  observe "changed_occurrence_not_cached_safe"
    (revised.occurrence.statementIdentity == changed.statementIdentity &&
      (observedAssessments (← getEnv)).size == before + 1)
  setEnv primed
  let unrelated := TemplateAudit.sourcePath `LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected
  let bytes ← IO.FS.readBinFile unrelated
  try
    IO.FS.writeFile unrelated ((String.fromUTF8! bytes) ++ "\n-- changed unrelated enrollment input\n")
    let unchanged ← assessJoined
    observe "unrelated_template_keeps_selected_evidence"
      (unchanged.all (fun row => row.result matches .declaredValidated _) &&
        (observedAssessments (← getEnv)).size == before)
  finally IO.FS.writeBinFile unrelated bytes
  setEnv primed
  setReducibilityStatus plan.name .irreducible
  discard <| assessJoined
  observe "changed_native_metadata_not_cached_safe"
    ((observedAssessments (← getEnv)).size == before + 1)
  setEnv primed
  let lowered ← withOptions (fun options => informationTemplate.work.set options 1) assessJoined
  observe "changed_options_not_cached_safe"
    (lowered.all (fun row => row.result matches .declaredUnresolved _) &&
      (observedAssessments (← getEnv)).size == before + 1)
  setEnv primed
  let changedClaim : TemplateBindingClaim := { claim with descriptor := some (mkConst ``Bool.true) }
  let changedRecord ← assess record.occurrence (some changedClaim)
  observe "changed_claim_not_cached_safe"
    ((changedRecord.result matches .declaredUnresolved _) &&
      (observedAssessments (← getEnv)).size == before + 1)
  setEnv initial

end LeanInformationAudit.Tests.DeclaredAssessmentCache
