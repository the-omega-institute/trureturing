import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Diagnostic switches preserve successful assignments and kernel certificates. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd liftTermElabM do
  let index ← DiskLookup.openIndex
    "build/lean-inspector/lookup-index/lookup-fixture" "lookup-fixture"
    "56a005855ea17e0b0958f73ec801ae140b0a1679"
  let table : LookupTable := {environment := ← getEnv, disk? := some index}
  let target := mkApp (mkConst ``Mark) (mkNatLit 9)
  let named ← replayCertificate target [] (.lookup ``pair) (some table)
  let result ← localRebuild target [] (some table)
  unless named.cost == .zero && named.proof?.isSome &&
      result.cost == .zero && result.proof?.isSome do
    throwError "telemetry changed the Mark 9 lookup certificate: {result.detail}"
  checkLocalProof target result.proof?.get!
  logInfo s!"LOOKUP_TELEMETRY cost=zero kernel=true source={result.lookup.source?} complete={result.lookup.complete}"

run_cmd liftTermElabM do
  let index ← DiskLookup.openIndex
    "build/lean-inspector/lookup-index/lookup-fixture" "lookup-fixture"
    "56a005855ea17e0b0958f73ec801ae140b0a1679"
  let target ← Term.elabType (← `(Mark 9 ∧ (First → Last)))
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let bucket := hash (DiscrTree.Key.const ``Mark 1)
  let files := index.manifest.find? (fun item => item.1 == bucket) |>.map (·.2) |>.getD #[]
  unless !files.isEmpty do throwError "missing Mark fixture shard"
  let broken := {index with manifest := index.manifest.map fun (key, names) =>
    if key == bucket then (key, #["b1-missing-page.pickle"]) else (key, names)}
  let table : LookupTable := {environment := ← getEnv, disk? := some broken}
  let root ← mkFreshExprMVar target
  let parent ← lookupLeaf table root.mvarId! (fun _ => pure false) (fun _ => pure false)
  unless parent.complete && parent.source?.isNone do
    throwError "B1 counterfactual parent enumeration did not exhaust normally"
  let result ← localRebuild target [] (some table)
  unless result.cost == .unknown && !result.lookup.complete &&
      result.lookup.failures.contains "B1:split-incomplete" do
    throwError "B1 mutation accepted: incomplete split became NoHit: {result.detail}"
  logInfo "LOOKUP_B1_MECHANISM parent=one split=unknown incomplete_preserved=true"
