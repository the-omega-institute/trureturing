import LeanInformationAuditRegAnalysis.SearchReduction.Local
import LeanInformationAuditRegTests.SearchReduction.GraphCandidates

open Lean Meta Elab Command LeanInformationAudit.SearchReduction

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Lean}] {} 0 (leakEnv := true) (loadExts := true)
  liftTermElabM do
    let source ← getEnv
    let squareFact ← getConstInfo ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareFact
    let added := #[(squareFact.type, mkConst squareFact.name)]
    for name in #[
        ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.square,
        ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.scopedWitness,
        ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.nested,
        ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.splitHelper,
        ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.dead] do
      let info ← getConstInfo name
      let some value := info.value? (allowOpaque := true) | throwError "missing fixture body"
      let graph ← withEnv source <| extractGraph base info.type value added
      let reading ← withEnv base <| evaluateGraph graph
      let checked? ← withEnv source <| assembleZero reading.graph true
      logInfo m!"graph-calibration {name}: nodes={reading.graph.vertices.length} edges={reading.graph.edges.length} complete={reading.graph.complete} issues={reading.graph.issues} B={reprStr reading.baseline} BS={reprStr reading.paired} vis={reprStr reading.baselineVisible} k1BS={reprStr reading.pairedK1} probes={reprStr reading.baselineProbe.outcome}/{reprStr reading.pairedProbe.outcome} usesS={reading.pairedUsesSeed} checked={checked?.isSome} verdict={reprStr (classifyGraph {reading with isolated := true, structureChecked := true, structureClean := true, presentationComplete := true})}"
      let certified := {reading with isolated := true, structureChecked := true, structureClean := true, presentationComplete := true}
      unless reading.graph.complete do throwError "unexpected incomplete calibration graph"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.scopedWitness then
        unless reading.baseline == ⟨.finite 0, .finite 0⟩ && classifyGraph certified == .bindOnly && checked?.isSome do
          throwError "scoped-variable calibration failed"
      else if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.nested then
        unless reading.baseline == ⟨.finite 2, .finite 2⟩ && reading.paired == ⟨.finite 1, .finite 1⟩ &&
            classifyGraph certified == .nonBindOnly && classifyClosure certified == some .partial_ do
          throwError "nested-witness partial-reduction calibration failed"
      else
        unless reading.baseline == ⟨.finite 1, .finite 1⟩ && reading.paired == ⟨.finite 0, .finite 0⟩ &&
            reading.baselineVisible == ⟨.finite 0, .finite 0⟩ && classifyGraph certified == .nonBindOnly &&
            classifyClosure certified == some .zero && checked?.isSome do
          throwError "hidden-witness zero-closure calibration failed"
      for edge in reading.graph.edges do
        logInfo m!"edge {edge.conclusion} <- {edge.premises} head={edge.source} k={edge.window} cost={reprStr edge.cost}/{reprStr edge.pairedCost} {edge.detail}"
