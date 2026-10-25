import LeanInformationAuditRegAnalysis.SearchReduction.Commands

open Lean Meta Elab Command LeanInformationAudit.SearchReduction

namespace LeanInformationAudit.Tests.SearchReduction

structure CacheFixture where
  identity : String
  directory : System.FilePath
  request : Request
  result : Observation

def CacheFixture.write (f : CacheFixture) (result : Observation) : IO Unit :=
  pickle (f.directory / s!"probe-{hash f.identity}.pickle")
    ({identity := f.identity, targetHeader := ([], mkConst ``True), result} : ProbeCacheRecord)

/-- Each replay case owns a compiler process, which releases imported regions on exit. -/
unsafe def withCacheFixture (action : CacheFixture → CommandElabM Unit) : CommandElabM Unit := do
  let original ← getEnv
  let identity := s!"cache-replay-regression-{← IO.monoNanosNow}"
  let directory : System.FilePath := "build/lean-inspector/" ++ identity
  let request : Request := {
    target := ``True.intro, «baseline» := #[], baselineCommit := "cache-regression" }
  let result : Observation := {
    target := request.target, base := .incomplete .undecided,
    paired := .incomplete .undecided, verdict := .insufficient }
  try
    saveProbeCache directory identity original request result
    action {identity, directory, request, result}
  finally modifyEnv fun _ => original

end LeanInformationAudit.Tests.SearchReduction
