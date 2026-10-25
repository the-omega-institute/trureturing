import LeanInformationAuditRegTests.SearchReduction.ProbeCacheFixture

/-! Live replay of serialized certificates and imported dependency modules. -/

open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

run_cmd withCacheFixture fun f => do
  unless ← replayProbeCache f.directory f.identity f.request #[] `cacheReplayValid do
    throwError "live cache replay did not read a saved record"
  logInfo "live probe replay: saved data loaded and kernel publication completed"

/- Imported dependency modules remove repeated dependency kernel work while
leaving certificate checks and fresh classifier publication on the live path. -/
run_cmd do
  withCacheFixture fun f => do
    let original ← getEnv
    let module ← liftTermElabM <|
      writeCacheDependencyModule f.directory f.identity original f.dependencies
    pickle (f.directory / s!"probe-{hash f.identity}.pickle")
      ({identity := f.identity, targetHeader := ([], mkConst ``True),
        result := f.result, dependencies := f.dependencies,
        dependencyModule? := some module} : ProbeCacheRecord)
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
