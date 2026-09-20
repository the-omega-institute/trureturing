import LeanInformationAudit.Tests.Occurrence.ImportedArenaAlignmentRegistration

open Lean Lean.Elab.Command LeanInformationAudit

-- The evidence-only resolver must retain the corrected owner after native import.
run_cmd do
  let actual ← liftTermElabM <| resolveCanonicalArenaNameFromEvidence `QualityContext.drift
  unless actual == `QualityContext.drift do
    throwError "[FAIL] QUALITY-CONTEXT-EVIDENCE expected=QualityContext.drift actual={actual}"
  let some entry := InformationRegistry.find? (← getEnv) `QualityRegistration.contextFact
    | throwError "missing imported registration"
  unless entry.canonicalObjectArenaName == actual do
    throwError "[FAIL] QUALITY-CONTEXT imported registration/evidence disagree"
  unless (InformationRegistry.find? (← getEnv) `QualityRegistration.defaultFact).isNone do
    throwError "[FAIL] QUALITY-DEFAULT imported a rejected registration"
  logInfo "[PASS] QUALITY-CONTEXT-EVIDENCE owner=QualityContext.drift"

/-- error: IE-C003 ArenaSourceUnsupported arena=QualityPure.defaultUse owner=QualityPure.defaultUse -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence `QualityPure.defaultUse

/-- error: IE-C003 ArenaSourceUnsupported arena=QualityPure.defaultTailUse owner=QualityPure.defaultTailUse -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence `QualityPure.defaultTailUse

/-- error: IE-C003 ArenaSourceUnsupported arena=QualityPure.inferredUse owner=QualityPure.inferredUse -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence `QualityPure.inferredUse

/-- error: IE-C003 ArenaSourceUnsupported arena=QualityPure.localImplicitDefaultUse owner=QualityPure.localImplicitDefaultUse -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <|
    resolveCanonicalArenaNameFromEvidence `QualityPure.localImplicitDefaultUse

/-- error: IE-C003 ArenaSourceUnsupported arena=QualityContext.unresolved owner=QualityContext.unresolved -/
#guard_msgs (error) in
run_cmd do
  discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence `QualityContext.unresolved

run_cmd do
  for name in #[`QualityPure.deadDefaultUse, `QualityPure.deadDefaultTailUse,
      `QualityPure.localImplicitDeadDefaultUse,
      `QualityPure.deadInferredUse, `QualityContext.directAlias,
      `QualityContext.classAlias, `QualityContext.qualifiedClassAlias] do
    unless (← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name) ==
        `ProvenanceProbe.arena do
      throwError "[FAIL] dead argument/class-let imported evidence: {name}"
  logInfo "[PASS] QUALITY-DEFAULT-EVIDENCE rejected IE-C003; \
    dead arguments retain ProvenanceProbe.arena"
