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


run_cmd do
  for name in #[`QualityGrouped.shifted, `QualityGrouped.shiftedCopy] do
    let diagnostic ← liftTermElabM do
      try return s!"accepted owner={← resolveCanonicalArenaNameFromEvidence name}"
      catch ex => ex.toMessageData.toString
    unless diagnostic == s!"IE-C003 ArenaSourceUnsupported arena={name} owner={name}" do
      throwError "[FAIL] grouped native evidence: {diagnostic}"
  for name in #[`QualityGroupedRegistration.aliasFact, `QualityGroupedRegistration.copyFact] do
    unless (InformationRegistry.find? (← getEnv) name).isNone do
      throwError "[FAIL] grouped rejected registration survived native import: {name}"
  for (name, expected) in #[
      (`QualityGrouped.deadInserted, `ProvenanceProbe.arena),
      (`QualityGrouped.liveOuter, `QualityGrouped.liveOuter),
      (`QualityGrouped.explicitInner, `ProvenanceProbe.arena),
      (`QualityGrouped.namedInner, `ProvenanceProbe.arena),
      (`QualityGrouped.groupedExplicit, `ProvenanceProbe.arena)] do
    unless (← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name) == expected do
      throwError "[FAIL] grouped native positive: {name}"
  logInfo "[PASS] Q3 dual evidence-only rejection/no insertion; grouped positives preserved"

run_cmd do
  for name in #[`ArchitectureNamed.deadUse, `ArchitectureNamed.explicitUse] do
    unless (← liftTermElabM <| resolveCanonicalArenaNameFromEvidence name) ==
        `ProvenanceProbe.arena do
      throwError "[FAIL] named dependency native evidence: {name}"
  let name := `ArchitectureNamed.liveUse
  let diagnostic ← liftTermElabM do
    try return s!"accepted owner={← resolveCanonicalArenaNameFromEvidence name}"
    catch ex => ex.toMessageData.toString
  unless diagnostic == s!"IE-C003 ArenaSourceUnsupported arena={name} owner={name}" do
    throwError "[FAIL] named live native evidence: {diagnostic}"
  unless (InformationRegistry.find? (← getEnv) `ArchitectureNamedRegistration.liveFact).isNone do
    throwError "[FAIL] named rejected registration survived native import"
  for name in #[`ArchitectureNamedRegistration.deadFact,
      `ArchitectureNamedRegistration.explicitFact] do
    let some entry := InformationRegistry.find? (← getEnv) name
      | throwError "[FAIL] missing named native registration: {name}"
    unless entry.canonicalObjectArenaName == `ProvenanceProbe.arena do
      throwError "[FAIL] named native registration owner: {name}"
  logInfo "[PASS] ARCH-Q3-001 native evidence dead/explicit owner=ProvenanceProbe.arena; \
    live rejected"
