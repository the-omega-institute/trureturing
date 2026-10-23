import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  enableInitializersExecution
  let imports : Array Import := #[{module := `Lean}]
  let (base, shared) ← withImporting do
    let (_, state) ← (importModulesCore imports).run default
    let base ← finalizeImport state imports {} 0 (leakEnv := false) (loadExts := true)
    pure (base, state)
  liftTermElabM do
    let source ← getEnv
    let index ← DiskLookup.openIndex "build/lean-inspector/lookup-index/lookup-fixture"
      "lookup-fixture" "56a005855ea17e0b0958f73ec801ae140b0a1679"
    let cases ← #[("membership", ← `(∀ n : Nat, Mark n ∧ Side)), ("nonrecursive", ← `(First → Last))].mapM fun (name, stx) => do
      let type ← Term.elabType stx
      Term.synthesizeSyntheticMVarsNoPostponing
      return (name, ← instantiateMVars type)
    let mut expected : Std.HashMap String String := {}
    for pass in [:4] do
      let table ← onDemandLookup {environment := base, disk? := some index} (some shared)
      for (name, type) in (if pass % 2 == 0 then cases else cases.reverse) do
        let bytes ← withEnv base do
          let type ← copyStatement source .anonymous type
          let graph : ProofGraph := {
            root := 0, vertices := [{id := 0, type}],
            edges := [{conclusion := 0}], complete := true}
          let reading ← evaluateGraph graph (some table)
          let baselineProof? ← assembleZero reading.graph
          let pairedProof? ← assembleZero reading.graph true
          let reading := {reading with
            baselineProof?, pairedProof?,
            isolated := true, structureChecked := true,
            structureClean := true, presentationComplete := true}
          if name == "membership" then
            unless reading.baseline == ⟨.finite 0, .finite 0⟩ &&
                reading.baselineProof?.isSome do
              throwError "external membership determinism case did not certify a positive hit"
          let observation : Observation := {
            target := name.toName, graph? := some reading,
            verdict := classifyGraph reading, base := reading.baselineProbe.outcome,
            paired := reading.pairedProbe.outcome}
          return (observationJson observation).compress
        if let some previous := expected[name]? then
          unless bytes.toUTF8 == previous.toUTF8 do
            throwError "cold/warm forward/reverse byte mismatch: {name} pass={pass}"
        else expected := expected.insert name bytes
        IO.eprintln s!"LOOKUP_DETERMINISM case={name} pass={pass} bytes={bytes}"
    logInfo "LOOKUP_DETERMINISM_ACCEPTED cold_warm=true forward_reverse=true per_query_json_bytes=true cases=2 passes=4"
