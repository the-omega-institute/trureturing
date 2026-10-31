import LeanInformationAuditRegAnalysis.SearchReduction.Commands

open Lean Meta Elab Command LeanInformationAudit.SearchReduction

namespace LeanInformationAudit.Tests.SearchReduction

structure CacheFixture where
  identity : String
  directory : System.FilePath
  request : Request
  result : Observation
  dependencies : Array Declaration

def CacheFixture.write (f : CacheFixture) (result : Observation)
    (rejection? : Option ProbeRejection := none) : IO Unit :=
  pickle (f.directory / s!"probe-{hash f.identity}.pickle")
    ({
      identity := f.identity
      targetHeader := ([], mkConst ``True)
      outcome := match rejection? with
        | some rejection => .rejected f.request.target (sourceAuditEvidence result) rejection
        | none => .observed result
      dependencies := f.dependencies} : ProbeCacheRecord)

/-- Each replay case owns a compiler process, which releases imported regions on exit. -/
unsafe def withCacheFixture (action : CacheFixture → CommandElabM Unit) : CommandElabM Unit := do
  let original ← getEnv
  let target := `cacheFixtureTarget
  let auxiliary := `cacheFixtureAux
  liftTermElabM do
    for name in #[target, auxiliary] do
      discard <| checkProof name [] (mkConst ``True) (mkConst ``True.intro)
  let source ← getEnv
  let identity := s!"cache-replay-regression-{← IO.monoNanosNow}"
  let directory : System.FilePath := "build/lean-inspector/" ++ identity
  let request : Request := {
    target, «baseline» := #[], baselineCommit := "cache-regression" }
  let result : Observation := {
    target := request.target, base := .incomplete .undecided,
    paired := .incomplete .undecided, verdict := .insufficient
    attempts := #[{strategy := "cached", outcome := .found, proof? := some (mkConst auxiliary)}] }
  let dependencies ← match captureCacheDependencies source original target #[auxiliary] with
    | .ok declarations => pure declarations
    | .error message => throwError "{message}"
  try
    saveProbeCache directory identity source request result (some original)
    modifyEnv fun _ => original
    action {identity, directory, request, result, dependencies}
  finally modifyEnv fun _ => original

end LeanInformationAudit.Tests.SearchReduction
