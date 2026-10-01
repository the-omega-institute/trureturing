import LeanInformationAudit.ContractPrototype.Discovery
import LeanInformationAudit.ContractPrototype.Companions
import LeanInformationAudit.SealCommand

/- L0 原型 -/
namespace LeanInformationAudit.ContractPrototype
open Lean Meta Elab Command

private def command (action : CommandElabM Unit) : MetaM Unit :=
  liftM (liftCommandElabM action : CoreM Unit)

/-- Discovery is shared; selection, template plans and assessments are rooted at
one target. No report hook executes while Reg is compiled. -/
def replay (root : Name) (snapshot : Snapshot)
    (checkpoint : String → MetaM Unit := fun _ => pure ()) : MetaM Unit := do
  let saved ← getEnv
  tryCatchRuntimeEx (do
    let reachable := reachableModules saved root
    let selected (owner : Name) := reachable.contains owner
    let registrations := snapshot.registrations.filter (selected ∘ Prod.fst)
    let enrollments := snapshot.enrollments.filter (selected ∘ Prod.fst)
    let contracts := snapshot.roots.filter (selected ∘ Prod.fst)
    let mut seen : NameSet := {}
    for (owner, contract) in contracts do
      unless owner == contract.rootId do throwError "IE-C028 RootContractOwnerMismatch: {contract.rootId}"
      if seen.contains owner then throwError "IE-C028 DuplicateRootContract: {owner}"
      seen := seen.insert owner
      command <| RootCatalogs.declare contract
      checkpoint "root"
    for (owner, expected) in snapshot.expected do
      unless selected owner do continue
      unless owner == expected.rootId do throwError "incomplete_closure:dtr.expected_owner"
      modifyEnv (ExpectedOccurrenceManifest.addEntry · expected)
      checkpoint "expectation"
    for (owner, payload) in snapshot.companions do
      if selected owner then
        GeneratedDeclarations.withOwner owner <| prepareCompanions owner payload.input payload
        checkpoint "companions"
    modifyEnv fun env => TemplateAudit.resetTemplatePlans <|
      TemplateBinding.resetAssessmentRecords <| InformationRegistry.reset env
    checkpoint "reset"
    command <| do
      for (_, contract) in contracts do
        liftTermElabM <| RootCatalogs.acquireProvenance contract
      for (owner, expected) in snapshot.expected do
        if selected owner then
          discard <| liftTermElabM <| resolveCanonicalArenaName expected.objectArenaName
      for (owner, enrollment) in enrollments do
        unless owner == enrollment.owner do throwError "incomplete_closure:E7.import_owner"
        assessRecordedEnrollment owner enrollment
      for (owner, registration) in registrations do
        unless owner == registration.entry.registrationModuleName do
          throwError "incomplete_closure:dtr.input_owner"
        GeneratedDeclarations.withOwner owner <| assessRecordedEntry owner registration
    checkpoint "assessment"
    seen := {}
    for (owner, request) in snapshot.seals do
      unless selected owner do continue
      unless owner == request.rootId do throwError "incomplete_closure:dtr.seal_owner"
      if seen.contains owner then throwError "incomplete_closure:dtr.duplicate_seal"
      seen := seen.insert owner
      withOptions (fun _ => request.options) <| GeneratedDeclarations.withOwner owner do
        liftM (assessAndSealRegistration (← RegistrationAssessmentInput.capture owner) : CoreM Unit)
      checkpoint "seal"
  ) fun error => do
    setEnv saved
    throw error

/-- The L0 driver reads typed declarations only for prototype targets; the
recorder path is preserved for the original targets used as controls. -/
def reports (targets : Array Name) : MetaM (Array (Json × Array Name × Environment)) := do
  let snapshot ← discover targets
  let owners := snapshot.registrations.map Prod.fst ++ snapshot.enrollments.map Prod.fst ++
    snapshot.seals.map Prod.fst ++ snapshot.roots.map Prod.fst ++ snapshot.expected.map Prod.fst
  assessReportTargets targets (owners ++ recordedInputOwners (← getEnv)) fun target => do
    if owners.any (reachableModules (← getEnv) target).contains then
      replay target snapshot
    else
      assessRecordedRegistrations target
    return registeredKeys (← getEnv) target

end LeanInformationAudit.ContractPrototype
