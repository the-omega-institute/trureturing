import LeanInformationAuditRegTests.SearchReduction.ProbeCacheFixture

open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

run_cmd withCacheFixture fun f => do
  f.write {f.result with verdict := .bindOnly}
  let rejected ← try
    discard <| replayProbeCache f.directory f.identity f.request #[] `cacheReplayInvalidVerdict
    pure false
    catch _ => pure true
  unless rejected do throwError "live cache replay accepted an altered verdict"
  logInfo "live probe replay: altered verdict rejected by kernel"
