import Mathlib
import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.GraphCandidates
import LeanInformationAuditRegTests.SearchReduction.Candidates

/-! Calibration on mechanically extracted declaration graphs. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction

set_option Elab.async false

run_cmd liftTermElabM do
  let target ← Term.elabType (← `(∀ (α : Type) (P : α → Prop),
    (∃ x, P x) → ∃ x, P x ∧ P x))
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let result ← localRebuild target
  unless result.cost == .zero && result.proof?.isSome do
    throwError "Exists elimination failed: {result.detail}"
  logInfo "local-calibration Exists elimination: kernel-checked zero"

run_cmd do
  enableInitializersExecution
  let base ← importModules #[{module := `Mathlib}] {} 0 (leakEnv := true) (loadExts := true)
  liftTermElabM do
    let source ← getEnv
    let square := ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareFact
    let addition := ``LeanInformationAudit.Tests.SearchReduction.Candidates.addition
    let fixtures := #[
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.scopedApply, #[]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.helperApplications, #[]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia, #[square]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.twoLayerVia, #[square]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.scopedWitness, #[square]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.splitHelper, #[square]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.dead, #[square]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.routineVia, #[]),
      (``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContent, #[addition]),
      (``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContentWithoutOmega,
        #[``LeanInformationAudit.Tests.SearchReduction.Candidates.additionWithoutOmega])]
    let mut positives := 0
    let mut bindings := 0
    let mut doubled : Option GraphReading := none
    for (name, additions) in fixtures do
      let graph ← withEnv source <| extractGraph base name additions
      for v in graph.vertices do
        if v.seed then continue
        let some n := v.origin.constName? | throwError "unnamed declaration vertex"
        unless allowCompletion source n && !isMatcherCore source n &&
            !(← withEnv source <| isEqnThm n) do
          throwError "compiler auxiliary retained as an author vertex: {n}"
        if n.toString.startsWith "Lean.Omega." then
          throwError "Omega certificate retained as a nonseed vertex: {n}"
      -- Rebuild only statement vocabulary before any local probe.
      let reading ← withEnv base do
        for v in graph.vertices do
          for dep in v.type.getUsedConstants do copyVocabulary source dep
        evaluateGraph graph
      let certified := {reading with
        isolated := true, structureChecked := true,
        structureClean := true, presentationComplete := true}
      let verdict := classifyGraph certified
      if verdict == .bindOnly then bindings := bindings + 1
      if verdict == .nonBindOnly then positives := positives + 1
      let observation : Observation := {
        target := name, base := reading.baselineProbe.outcome,
        paired := reading.pairedProbe.outcome, verdict, graph? := some certified,
        configuration := localConfiguration}
      logInfo s!"DECL_FIXTURE {observationJson observation |>.compress}"
      unless graph.complete do throwError "incomplete declaration fixture {name}: {graph.issues}"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.dead then
        unless reading.noAuxiliary && verdict != .nonBindOnly do
          throwError "dead helper acquired a positive verdict"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia then
        let synthetic := reading.graph.edges.any fun edge =>
          edge.premises.any fun p =>
            (reading.graph.vertices.find? (·.id == p)).any fun v =>
              v.origin.constName? == some square && !edge.analytic.contains p
        unless synthetic do throwError "squareFact was not classified synthetic"
        let predicted := reading.baseline == ⟨.finite 1, .finite 1⟩ &&
          reading.paired == ⟨.finite 0, .finite 0⟩ && classifyClosure certified == some .zero
        logInfo s!"DECL_PREDICTION squareVia {predicted}"
        unless predicted do throwError "squareVia prediction failed"
        unless reading.graph.vertices.any (fun v =>
            v.origin.constName? == some square && !v.targetPart) do
          throwError "independently routine squareFact excluded as target-part"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.twoLayerVia then
        let predicted := reading.baseline == ⟨.finite 2, .finite 2⟩ &&
          reading.paired == ⟨.finite 1, .finite 1⟩ && classifyClosure certified == some .partial_
        logInfo s!"DECL_PREDICTION twoLayerVia {predicted}"
      if name == ``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContent then
        doubled := some reading
        let predicted := (reading.baseline == ⟨.finite 1, .finite 1⟩ ||
          reading.baseline == ⟨.finite 2, .finite 2⟩) && strictDrop reading.baseline reading.paired &&
          classifyClosure certified == some .zero
        logInfo s!"DECL_PREDICTION doubledContent {predicted}"
      if name == ``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContentWithoutOmega then
        logInfo s!"DECL_CLOSER_INVARIANCE {doubled.any (fun old =>
          old.baseline == reading.baseline && old.paired == reading.paired)}"
    logInfo s!"DECL_CALIBRATION non_bind_only={positives} bind_only={bindings}"
