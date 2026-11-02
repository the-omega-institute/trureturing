import LeanInformationAuditRegTests.SearchReduction.ProbeCacheFixture

open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction

run_cmd withCacheFixture fun f => do
  let invalid := mkApp
    (mkLambda `h .default (mkConst ``False) (mkBVar 0)) (mkConst ``True.intro)
  f.write {f.result with attempts := #[{
    strategy := "cached", outcome := .found, proof? := some invalid}]}
  let rejected ← try
    discard <| replayProbeCache f.directory f.identity f.request #[] `cacheReplayInvalidCertificate
    pure false
    catch _ => pure true
  unless rejected do throwError "live cache replay accepted an invalid certificate"
  logInfo "live probe replay: invalid certificate rejected by kernel"
