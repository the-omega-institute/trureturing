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
