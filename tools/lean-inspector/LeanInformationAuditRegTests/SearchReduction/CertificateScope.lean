import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! A named certificate cannot escape the production primary-index B_T scope. -/

open Lean Meta Elab Command LeanInformationAudit.SearchReduction
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  enableInitializersExecution
  let base ← importModules
    #[{module := `LeanInformationAuditRegTests.SearchReduction.LookupBaseline}] {} 0
    (leakEnv := false) (loadExts := true)
  let index ← DiskLookup.openFixtureIndex "build/lean-inspector/search-reduction-test-index/lookup-fixture"
    "lookup-fixture" "56a005855ea17e0b0958f73ec801ae140b0a1679"
  liftTermElabM <| withEnv base do
    let target := mkApp (mkConst
      ``LeanInformationAudit.Tests.SearchReduction.LookupBaseline.Mark) (toExpr (9 : Nat))
    let certificate := ObviousCertificate.lookup
      ``LeanInformationAudit.Tests.SearchReduction.LookupBaseline.pair
    let allowed ← replayCertificate target [] certificate (some {environment := base, disk? := some index})
    unless allowed.cost == .zero && allowed.proof?.isSome do
      throwError "in-scope primary candidate did not replay: {allowed.detail}"
    checkLocalProof target allowed.proof?.get!
    let excluded ← replayCertificate target [] certificate
      (some {environment := base, disk? := some index, implicationModules? := some #[]})
    unless excluded.cost == .unknown && excluded.proof?.isNone do
      throwError "mutation accepted: actual-out-of-scope-name"
    logInfo "CERT_MUTATION rejected actual-out-of-scope-name with positive control"
