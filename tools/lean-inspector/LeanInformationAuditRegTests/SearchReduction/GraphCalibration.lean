import Mathlib
import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.GraphCandidates
import LeanInformationAuditRegTests.SearchReduction.Candidates

/-! Calibration on mechanically extracted declaration graphs. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction

set_option Elab.async false

private instance (a b : Bound) : Decidable (a ≤ b) := by
  change Decidable (boundLe a b)
  cases a <;> cases b <;> dsimp [boundLe] <;> infer_instance

private def assertDeclPrediction (name : String) (predicted : Bool) : TermElabM Unit := do
  logInfo s!"DECL_PREDICTION {name} {predicted}"
  unless predicted do throwError "declaration prediction failed: {name}"

/--
info: DECL_PREDICTION false-regression false
---
error: declaration prediction failed: false-regression
-/
#guard_msgs in
run_cmd liftTermElabM do
  assertDeclPrediction "false-regression" false

run_cmd liftTermElabM do
  let target ← Term.elabType (← `(∀ (α : Type) (P : α → Prop),
    (∃ x, P x) → ∃ x, P x ∧ P x))
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let result ← localRebuild target
  unless result.cost == .zero && result.proof?.isSome do
    throwError "Exists elimination failed: {result.detail}"
  logInfo "local-calibration Exists elimination: kernel-checked zero"

-- Each localRebuild retains its own fixed budget. The aggregate fixture
-- command must not share one budget across unrelated queries.
set_option maxHeartbeats 0 in
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
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squaredWitness,
        #[``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.splitHelper, #[square]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.dead, #[square]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.routineVia, #[]),
      (``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContent, #[addition]),
      (``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContentWithoutOmega,
        #[``LeanInformationAudit.Tests.SearchReduction.Candidates.additionWithoutOmega]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.sharedRoutine, #[]),
      (``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.sharedWitness, #[])]
    let mut positives := 0
    let mut bindings := 0
    let mut sharedTable : Array Nat := #[0, 0, 0, 0]
    let mut missingShared := 0
    let mut unknownCost := 0
    let mut noAuxiliary := 0
    let mut opaqueCount := 0
    let mut doubled : Option GraphReading := none
    for (name, additions) in fixtures do
      let delivery := (#[name] ++ additions).filterMap fun n =>
        (source.getModuleIdxFor? n).map fun i => source.header.moduleNames[i.toNat]!
      let scope ← targetBaselineImports "b02b98342945a1a724a227db4fa38e376640e573"
        delivery source name #[]
      let table ← onDemandLookup {environment := base, fixture := true, implicationModules? := some scope}
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
        let vertices ← graph.vertices.mapM fun v => do
          return {v with type := ← copyStatement source (v.origin.constName?.getD .anonymous) v.type}
        evaluateGraph {graph with vertices} (some table)
      let certified := {reading with
        isolated := true, structureChecked := true,
        structureClean := true, presentationComplete := true}
      let verdict := classifyGraph certified
      if reading.noAuxiliary then noAuxiliary := noAuxiliary + 1
      opaqueCount := opaqueCount + (reading.graph.vertices.filter (·.opaqueDecl)).length
      for edge in reading.graph.edges do
        unless edgeActive edge do continue
        match edge.sharedData?, edge.cost with
        | none, _ => missingShared := missingShared + 1
        | _, .unknown => unknownCost := unknownCost + 1
        | some shared, cost =>
          let cell := (if shared then 2 else 0) + (if cost == .one then 1 else 0)
          sharedTable := sharedTable.modify cell (· + 1)
      if verdict == .bindOnly then bindings := bindings + 1
      if verdict == .nonBindOnly then positives := positives + 1
      let observation : Observation := {
        target := name, base := reading.baselineProbe.outcome,
        paired := reading.pairedProbe.outcome, verdict, graph? := some certified,
        configuration := localConfiguration}
      logInfo s!"DECL_FIXTURE {observationJson observation |>.compress}"
      unless graph.complete do throwError "incomplete declaration fixture {name}: {graph.issues}"
      -- Dedicated native-event controls remain fixture observations, not admission.
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.scopedApply then
        assertDeclPrediction "trigger-allow-scopedApply" (verdict == .bindOnly)
        logInfo s!"SEARCH_REDUCTION_TRIGGER allow-scopedApply {(observationJson observation "b02b98342945a1a724a227db4fa38e376640e573").compress}"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.dead then
        unless reading.noAuxiliary && verdict != .nonBindOnly do
          throwError "dead helper acquired a positive verdict"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia then
        let synthetic := reading.graph.edges.any fun edge =>
          edge.premises.any fun p =>
            (reading.graph.vertices.find? (·.id == p)).any fun v =>
              v.origin.constName? == some square && !edge.analytic.contains p
        unless synthetic do throwError "squareFact was not classified synthetic"
        let some owner := base.getModuleIdxFor? ``Nat.exists_mul_self
          | throwError "Nat.exists_mul_self owner missing from fixture environment"
        unless !scope.contains base.header.moduleNames[owner.toNat]! do
          throwError "incidental Mathlib import enlarged squareVia's B_T"
        let predicted := reading.baseline == ⟨.finite 1, .finite 1⟩ &&
          reading.paired == ⟨.finite 0, .finite 0⟩ && verdict == .nonBindOnly &&
          classifyClosure certified == some .zero
        assertDeclPrediction "squareVia" predicted
        logInfo s!"SEARCH_REDUCTION_TRIGGER observe-squareVia {(observationJson observation "b02b98342945a1a724a227db4fa38e376640e573").compress}"
        unless reading.graph.vertices.any (fun v =>
            v.origin.constName? == some square && !v.targetPart) do
          throwError "independently routine squareFact excluded as target-part"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.twoLayerVia then
        let predicted := decide (reading.baseline.lower ≤ .finite 2 ∧
          .finite 2 ≤ reading.baseline.upper ∧ reading.paired.lower ≤ .finite 1 ∧
          .finite 1 ≤ reading.paired.upper) && strictDrop reading.baseline reading.paired &&
          verdict == .nonBindOnly && classifyClosure certified == some .partial_
        assertDeclPrediction "twoLayerVia" predicted
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squaredWitness then
        let predicted := strictDrop reading.baseline reading.paired &&
          verdict == .nonBindOnly && !reading.proofHardSeeds.isEmpty
        assertDeclPrediction "proof_hard" predicted
      if name == ``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContent then
        doubled := some reading
        let predicted := decide (.finite 1 ≤ reading.baseline.lower ∧
          reading.baseline.lower ≤ reading.baseline.upper ∧ reading.baseline.upper ≤ .finite 4) &&
          reading.paired == ⟨.finite 0, .finite 0⟩ && strictDrop reading.baseline reading.paired &&
          verdict == .nonBindOnly && classifyClosure certified == some .zero
        assertDeclPrediction "doubledContent" predicted
      if name == ``LeanInformationAudit.Tests.SearchReduction.Candidates.doubledContentWithoutOmega then
        logInfo s!"DECL_CLOSER_INVARIANCE {doubled.any (fun old =>
          old.baseline == reading.baseline && old.paired == reading.paired)}"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.sharedRoutine then
        let rootEdges := reading.graph.edges.filter (fun edge =>
          edge.conclusion == reading.graph.root)
        unless rootEdges.all (·.sharedData? == some true) &&
            reading.baseline == ⟨.finite 0, .finite 0⟩ do
          throwError "sharedRoutine static-sharing/zero-price prediction failed"
      if name == ``LeanInformationAudit.Tests.SearchReduction.GraphCandidates.sharedWitness then
        let rootEdges := reading.graph.edges.filter (fun edge =>
          edge.conclusion == reading.graph.root)
        unless rootEdges.all (·.sharedData? == some true) do
          throwError "sharedWitness static-sharing prediction failed"
        let predicted := decide (reading.baseline.lower ≤ .finite 1 ∧
          .finite 1 ≤ reading.baseline.upper ∧ reading.baseline.upper ≤ .finite 1 ∧
          reading.paired.lower ≤ .finite 1 ∧ .finite 1 ≤ reading.paired.upper ∧
          reading.paired.upper ≤ .finite 1) && verdict == .insufficient &&
          (classifyClosure certified).isNone
        assertDeclPrediction "sharedWitness" predicted
        logInfo s!"SEARCH_REDUCTION_TRIGGER observe-sharedWitness {(observationJson observation "b02b98342945a1a724a227db4fa38e376640e573").compress}"
        -- Publish the unchanged reading first; only its asserted verdict changes
        -- in the negative control. Both temporary environments are discarded.
        let publicationEnvironment ← getEnv
        withEnv publicationEnvironment do
          publish `integrationTriggerSharedWitness observation (some source)
          unless standardAxioms (← collectAxioms `integrationTriggerSharedWitness.verdictProof) do
            throwError "trigger publication used nonstandard axioms"
        let rejection ← withEnv publicationEnvironment do
          try
            publish `integrationTriggerSharedWitness
              {observation with verdict := .nonBindOnly} (some source)
            pure none
          catch error => pure (some (← error.toMessageData.toString))
        let some message := rejection
          | throwError "trigger rejected-verdict control was accepted"
        let normalized := String.intercalate " " <|
          ((message.replace "\n" " ").splitOn " ").filter (· != "")
        let expected := "Tactic `decide` proved that the proposition " ++
          "LeanInformationAudit.SearchReduction.classifyGraph " ++
          "integrationTriggerSharedWitness.graphReading = " ++
          "LeanInformationAudit.SearchReduction.Verdict.nonBindOnly is false"
        unless normalized == expected do
          throwError "trigger rejected-verdict control failed for another reason: {message}"
        if (← getEnv).contains `integrationTriggerSharedWitness then
          throwError "trigger temporary publication escaped its environment"
        logInfo s!"SEARCH_REDUCTION_TRIGGER reject-sharedWitness-verdict {message}"
    logInfo s!"DECL_CALIBRATION non_bind_only={positives} bind_only={bindings}"
    let table := Json.mkObj [
      ("configuration", toJson localConfiguration),
      ("population", toJson "all calibration candidate edges; baseline c"),
      ("shared_false", Json.mkObj [("c_zero", toJson sharedTable[0]!),
        ("c_one", toJson sharedTable[1]!)]),
      ("shared_true", Json.mkObj [("c_zero", toJson sharedTable[2]!),
        ("c_one", toJson sharedTable[3]!)]),
      ("unknown_cost", toJson unknownCost), ("missing_shared", toJson missingShared),
      ("no_auxiliary_declarations", toJson noAuxiliary),
      ("opaque_declarations", toJson opaqueCount)]
    logInfo s!"DECL_SHARED_DATA_TABLE {table.compress}"
    unless missingShared == 0 do throwError "missing static sharing annotation"
