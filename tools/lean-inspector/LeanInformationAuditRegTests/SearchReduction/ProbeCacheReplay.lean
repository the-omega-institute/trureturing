import LeanInformationAuditRegTests.SearchReduction.ProbeCacheFixture

open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

run_cmd withCacheFixture fun f => do
  unless ← replayProbeCache f.directory f.identity f.request #[] `cacheReplayValid do
    throwError "live cache replay did not read a saved record"
  logInfo "live probe replay: saved data loaded and kernel publication completed"
