import LeanInformationAuditRegTests.SearchReduction.ProbeCacheFixture

/-! Live replay of serialized certificates and imported dependency modules. -/

open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

run_cmd do
  let original ← getEnv
  let helper := `cacheInputHelper
  let target := `cacheInputRoot
  let request : Request := {target, «baseline» := #[`Mathlib], baselineCommit := "input-regression"}
  let build := fun (proof : Expr) => do
    modifyEnv fun _ => original
    liftTermElabM do
      discard <| checkProof helper [] (mkConst ``True) proof
      discard <| checkProof target [] (mkConst ``True) (mkConst helper)
    getEnv
  let inputs := fun source => match probeSourceInputs source request with
    | .ok value => pure value
    | .error message => throwError "{message}"
  try
    let first ← inputs (← build (mkConst ``True.intro))
    unless first == (← inputs (← getEnv)) do throwError "unchanged source data did not match"
    liftTermElabM do
      discard <| checkProof `unrelatedCurrentImplementation [] (mkConst ``True) (mkConst ``True.intro)
    unless first == (← inputs (← getEnv)) do
      throwError "unrelated current implementation entered source data identity"
    let different := mkApp
      (mkLambda `h .default (mkConst ``True) (mkBVar 0)) (mkConst ``True.intro)
    let changed ← inputs (← build different)
    if first == changed then throwError "changed transitive mathematical input was reused"
    logInfo "probe cache: exact transitive data changes invalidate; unrelated implementation does not"
  finally modifyEnv fun _ => original

run_cmd withCacheFixture fun f => do
  unless ← replayProbeCache f.directory f.identity f.request #[] `cacheReplayValid do
    throwError "live cache replay did not read a saved record"
  logInfo "live probe replay: saved data loaded and kernel publication completed"

/- Rejected records repeat the actual source guard, preserve its dependency,
and never publish a graph or verdict. An edited rejection is not evidence. -/
run_cmd withCacheFixture fun f => do
  let request := {f.request with additions := #[`cacheFixtureAux]}
  let result := {f.result with graph? := some {
    graph := {edges := [{conclusion := 0, zeroProof := some (mkConst `cacheFixtureAux)}]}
    queryRecords := [{role := "deferred", target := 0, premises := [], terminal := .notRun}] }}
  let rejection : ProbeRejection := {arm := .baseline, dependency := `cacheFixtureAux}
  unless (← auditProbeCertificates (← getEnv) request result) == some rejection do
    -- The replay environment has not installed the dependency yet. The guard
    -- rejects its forbidden name before attempting to resolve its body.
    throwError "source guard did not produce the exact typed rejection"
  let cacheBase ← getEnv
  liftTermElabM do
    replayCacheDependencies f.dependencies
    discard <| checkProof f.request.target [] (mkConst ``True) (mkConst ``True.intro)
  saveProbeCache f.directory f.identity (← getEnv) request result (some cacheBase)
    (rejection? := some rejection)
  modifyEnv fun _ => cacheBase
  let name := `cacheReplaySourceRejection
  let message ← try
    discard <| replayProbeCache f.directory f.identity request #[] name false
    pure "accepted"
    catch ex => ex.toMessageData.toString
  unless message == rejection.message do
    throwError "cached rejection changed: {message}"
  if (← getEnv).contains name || (← getEnv).contains (name ++ `graphReading) then
    throwError "source rejection published a verdict"
  for changed in [none, some {rejection with dependency := `differentDependency},
      some {rejection with arm := .paired}] do
    -- The observed-variant mutation must itself be fault-free, so the test
    -- specifically reaches the source-guard mismatch rather than fault refusal.
    let mutation := {result with graph? := result.graph?.map (fun g => {g with queryRecords := []})}
    f.write mutation changed
    let message ← try
      discard <| replayProbeCache f.directory f.identity request #[] name false
      pure "accepted"
      catch ex => ex.toMessageData.toString
    unless message == "search.probe_cache_rejection_mismatch" do
      throwError "altered rejection was not rejected: {message}"
  logInfo "probe cache: typed source rejection replayed, dependency rechecked, no publication"

run_cmd withCacheFixture fun f => do
  liftTermElabM do
    replayCacheDependencies f.dependencies
    discard <| checkProof f.request.target [] (mkConst ``True) (mkConst ``True.intro)
  let source ← getEnv
  let fault := {f.result with base := .incomplete .execution}
  let identity := f.identity ++ "-fault"
  for rejection? in [none, some {arm := SourceAuditArm.baseline, dependency := f.request.target}] do
    let rejected ← try
      saveProbeCache f.directory identity source f.request fault (rejection? := rejection?)
      pure false
      catch _ => pure true
    unless rejected do throwError "a fault was stored or relabeled as a source refusal"
  if ← (f.directory / s!"probe-{hash identity}.pickle").pathExists then
    throwError "fault cache record was written"
  logInfo "probe cache: ordinary fault cannot be stored or relabeled as a rejection"

run_cmd withCacheFixture fun f => do
  let rejected ← try
    discard <| replayProbeCache f.directory (f.identity ++ "-other-version") f.request #[]
      `cacheReplayOtherIdentity
    pure false
    catch _ => pure true
  -- A different identity selects a different path, so it is a miss.
  if rejected then throwError "different identity should miss before deserialization"
  let wrongPath := f.directory / s!"probe-{hash (f.identity ++ "-other-version")}.pickle"
  IO.FS.writeBinFile wrongPath
    (← IO.FS.readBinFile (f.directory / s!"probe-{hash f.identity}.pickle"))
  let rejected ← try
    discard <| replayProbeCache f.directory (f.identity ++ "-other-version") f.request #[]
      `cacheReplayOtherIdentity
    pure false
    catch _ => pure true
  unless rejected do throwError "mismatched typed identity was accepted"

/- Imported dependency modules remove repeated dependency kernel work while
leaving certificate checks and fresh classifier publication on the live path. -/
run_cmd do
  withCacheFixture fun f => do
    let original ← getEnv
    liftTermElabM do
      replayCacheDependencies f.dependencies
      discard <| checkProof f.request.target [] (mkConst ``True) (mkConst ``True.intro)
    let source ← getEnv
    saveProbeCache f.directory f.identity source f.request f.result
      (some original) (importDependencies := true) (moduleMinDependencies := 4096)
    modifyEnv fun _ => original
    profilePhase "regression/small-dependency-replay-start"
    unless ← replayProbeCache f.directory f.identity f.request #[] `cacheSmallDependencies do
      throwError "small dependencies did not use the live kernel replay path"
    if let some path ← IO.getEnv "SEARCH_REDUCTION_PROFILE" then
      let trace ← IO.FS.readFile path
      let trace := (trace.splitOn "regression/small-dependency-replay-start").getLast!
      unless (trace.splitOn "PROBE_CACHE_KERNEL_DEPENDENCIES count=1").length == 2 &&
          (trace.splitOn "PROBE_CACHE_IMPORTED_DEPENDENCIES").length == 1 do
        throwError "small dependency replay unnecessarily imported an export environment"
    modifyEnv fun _ => original
    saveProbeCache f.directory f.identity source f.request f.result
      (some original) (importDependencies := true)
    modifyEnv fun _ => original
    let module := s!"SearchReductionDependencies_{hash f.identity}" |>.toName
    let rejected ← try
      discard <| replayProbeCache f.directory f.identity f.request #[] `cacheModuleMissing
      pure false
      catch _ => pure true
    unless rejected do throwError "dependency module requirement was bypassed"
    let previousPath ← searchPathRef.get
    try
      searchPathRef.modify (f.directory :: ·)
      enableInitializersExecution
      let imported ← withImporting <|
        importModules #[{module}] options 0 (leakEnv := false) (loadExts := true)
      modifyEnv fun _ => imported.setMainModule original.mainModule
      profilePhase "regression/imported-dependency-replay-start"
      unless ← replayProbeCache f.directory f.identity f.request #[] `cacheModuleImported do
        throwError "checked dependency module did not replay"
      if let some path ← IO.getEnv "SEARCH_REDUCTION_PROFILE" then
        let trace ← IO.FS.readFile path
        let trace := (trace.splitOn "regression/imported-dependency-replay-start").getLast!
        unless (trace.splitOn "PROBE_CACHE_IMPORTED_DEPENDENCIES count=1").length == 2 &&
            (trace.splitOn "PROBE_CACHE_KERNEL_DEPENDENCIES").length == 1 &&
            (trace.splitOn "certificate/kernel/start").length > 1 &&
            (trace.splitOn "PROBE_CACHE hit=authenticated kernel_recomputed=true").length == 2 do
          throwError "imported replay repeated dependencies or skipped certificate/publication checks"
      logInfo "probe cache: imported module, rejected missing import, rechecked certificates"
    finally searchPathRef.set previousPath
