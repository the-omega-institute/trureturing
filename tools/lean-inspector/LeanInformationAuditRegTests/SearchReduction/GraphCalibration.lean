import LeanInformationAuditRegAnalysis.SearchReduction.Local
import LeanInformationAuditRegTests.SearchReduction.GraphCandidates

open Lean Meta Elab Command LeanInformationAudit.SearchReduction

set_option Elab.async false

run_cmd liftTermElabM do
  let target ← Term.elabType (← `(∀ (α : Type) (P : α → Prop),
    (∃ x, P x) → ∃ x, P x ∧ P x))
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let result ← localRebuild target none #[] [] []
  unless result.cost == .zero && result.proof?.isSome do
    throwError "Exists elimination failed: {result.detail}"
  logInfo "local-calibration Exists elimination: kernel-checked zero"

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Lean}] {} 0 (leakEnv := true) (loadExts := true)
  liftTermElabM do
    let source ← getEnv
    let scopedInfo ← getConstInfo ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.scopedApply
    let scopedGraph ← extractGraph base scopedInfo.type (scopedInfo.value? (allowOpaque := true)).get!.headBeta
    let scopedReading ← withEnv base <| evaluateGraph scopedGraph
    for edge in scopedReading.graph.edges do
      logInfo m!"scoped edge {edge.conclusion}: {reprStr edge.cost} {edge.detail}"
    logInfo m!"scoped interval {reprStr scopedReading.baseline}"
    unless scopedGraph.complete && scopedReading.baseline == ⟨.finite 0, .finite 0⟩ &&
        scopedReading.graph.edges.all (·.cost != .unknown) do
      throwError "scoped function application reconstruction failed: {scopedGraph.issues}"
    logInfo "local-calibration scoped application: complete, kernel-checked zero"
    let helperInfo ← getConstInfo ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.helperApplications
    let helperGraph ← extractGraph base helperInfo.type (helperInfo.value? (allowOpaque := true)).get!
    let helperEdges := helperGraph.edges.filter fun edge =>
      edge.source.any (fun name => name.getString! == "parametricHelper")
    unless helperEdges.length == 2 && helperEdges.all (fun edge =>
        edge.premises.head? == helperEdges.head!.premises.head?) do
      throwError "generic helper proof was duplicated across applications"
    let helperReading ← withEnv base <| evaluateGraph helperGraph
    unless helperReading.baseline == ⟨.finite 0, .finite 0⟩ do
      throwError "shared helper application reconstruction failed"
    logInfo "local-calibration generic helper: one shared proof, two checked calls"
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
