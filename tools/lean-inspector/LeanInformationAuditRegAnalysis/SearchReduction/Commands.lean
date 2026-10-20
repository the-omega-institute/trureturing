import LeanInformationAuditRegAnalysis.SearchReduction.Isolation

/-! Compiled Lean probe commands and a print-only JSON projection. -/

namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Command Tactic
open LeanInformationAudit.SearchReduction (Run Verdict)

-- Checked declarations may retain expressions from these small probe regions.
-- Their lifetime is the outer compiler process; no imported extension is read.
private initialize probeRegions : IO.Ref (Array CompactedRegion) ← IO.mkRef #[]

/-- Module bytes are immutable. The common import state contains only Mathlib;
source and baseline fork it before independently initializing extension state. -/
private def importSource (owners : Array Import) : IO (Environment × ImportState) :=
  withImporting do
    let (_, shared) ← (importModulesCore #[{module := `Mathlib}]).run default
    let (_, sourceState) ← (importModulesCore owners).run shared
    let source ← finalizeImport sourceState owners options 0
      (leakEnv := true) (loadExts := false)
    return (source, shared)

/-- The nested negative replay shares this probe's immutable module bytes.
The reference is cleared before returning; it never caches across targets. -/
private initialize activeProbe : IO.Ref (Option (Environment × ImportState)) ← IO.mkRef none


private def runJson : Run → Json
  | .found => toJson "found"
  | .exhausted => toJson "exhausted"
  | .incomplete failure => Json.mkObj [("incomplete", toJson (reprStr failure))]

private def verdictName : Verdict → String
  | .bindOnly => "bind-only[G,R_loc,k,B_used]"
  | .nonBindOnly => "non-bind-only[G,R_loc,k,B_used]"
  | .insufficient => "insufficient-evidence"

private def attemptJson (a : Attempt) : Json := Json.mkObj [
  ("strategy", toJson a.strategy), ("outcome", runJson a.outcome),
  ("axioms", toJson (a.axioms.map Name.toString)), ("detail", toJson a.detail),
  ("internal_heartbeats", toJson a.heartbeats)]

private def boundJson : Bound → Json
  | .finite n => toJson n
  | .top => toJson "infinity"

private def intervalJson (i : Interval) : Json := Json.mkObj [
  ("lower", boundJson i.lower), ("upper", boundJson i.upper)]

private def graphJson (r : GraphReading) : Json := Json.mkObj [
  ("k", toJson r.k), ("vertices", toJson r.graph.vertices.length),
  ("edges", toJson r.graph.edges.length), ("complete", toJson r.graph.complete),
  ("issues", toJson r.graph.issues),
  ("baseline_interval", intervalJson r.baseline),
  ("paired_interval", intervalJson r.paired),
  ("baseline_k1", intervalJson r.baselineK1), ("paired_k1", intervalJson r.pairedK1),
  ("baseline_visible", intervalJson r.baselineVisible), ("paired_visible", intervalJson r.pairedVisible),
  ("baseline_probe", runJson r.baselineProbe.outcome), ("paired_probe", runJson r.pairedProbe.outcome),
  ("baseline_zero_checked", toJson r.baselineProof?.isSome),
  ("paired_zero_checked", toJson r.pairedProof?.isSome),
  ("selected_seeds", toJson r.selectedSeeds),
  ("B_used", toJson (r.graph.vertices.filter (·.seed) |>.map fun v =>
    Json.mkObj [("id", toJson v.id), ("constant", toJson (v.origin.constName?.map Name.toString)),
      ("scoped", toJson (!v.scope.isEmpty))])),
  ("c_histogram", Json.mkObj (([EdgeCost.zero, .one, .unknown]).map fun c =>
    (reprStr c, toJson (r.graph.edges.filter (·.cost == c)).length))),
  ("priced_edges", toJson (r.graph.edges.map fun edge => Json.mkObj [
    ("conclusion", toJson edge.conclusion), ("premises", toJson edge.premises),
    ("head", toJson (edge.source.map Name.toString)), ("window", toJson edge.window),
    ("hidden_data_positions", toJson (edge.authorData.toList.zipIdx.filterMap
      (fun (data, index) => if data.isSome then some index else none))),
    ("cost", toJson (reprStr edge.cost)), ("paired_cost", toJson (reprStr edge.pairedCost)),
    ("detail", toJson edge.detail)])),
  ("paired_uses_seed", toJson r.pairedUsesSeed),
  ("verdict", toJson (reprStr (classifyGraph r))),
  ("closure", toJson ((classifyClosure r).map fun c =>
    match c with | .zero => "zero" | .partial_ => "partial"))]

/-- A human-readable projection. No code reads it back for classification. -/
def observationJson (r : Observation) (baselineCommit : String := "") : Json := Json.mkObj [
  ("reference", toJson "R_loc"), ("configuration", toJson r.configuration),
  ("scope", toJson r.scope), ("B_load_count", toJson r.loadedModules.size),
  ("B0_count", toJson r.catalogCount), ("B_load_subset_B0", toJson r.catalogVerified),
  ("B_load", toJson (r.loadedModules.map Name.toString)),
  ("B0_excluded", toJson (r.catalogExcluded.map Name.toString)),
  ("paired_structure_use", toJson (r.pairedStructureUse.map Name.toString)), ("baseline_commit", toJson baselineCommit),
  ("mathlib", toJson mathlibRevision), ("maxHeartbeats", toJson budget),
  ("target", toJson r.target.toString), ("verdict", toJson (if r.verdict == .nonBindOnly then s!"non-bind-only[G,R_loc,k; {r.scope}]" else verdictName r.verdict)),
  ("baseline", runJson r.base), ("paired", runJson r.paired),
  ("presentation", runJson r.presentation),
  ("presentation_source", toJson (r.presentationEvidence?.map (·.source.toString))),
  ("presentation_axioms", toJson (r.presentationEvidence?.map (·.axioms.map Name.toString))),
  ("presentation_detail", toJson r.presentationDetail),
  ("target_checked", toJson r.targetChecked),
  ("structure_checked", toJson r.structureChecked),
  ("structure_clean", toJson r.structureClean),
  ("attempt_count", toJson r.attempts.size),
  ("paired_attempt_count", toJson r.pairAttempts.size),
  ("attempts", Json.arr (r.attempts.map attemptJson)),
  ("paired_attempts", Json.arr (r.pairAttempts.map attemptJson)), ("reason", toJson r.reason),
  ("graph", toJson (r.graph?.map graphJson))]

private def runExpr : Run → Expr
  | .found => mkConst ``Run.found
  | .exhausted => mkConst ``Run.exhausted
  | .incomplete failure => mkApp (mkConst ``Run.incomplete)
      (mkConst <| match failure with
        | .missing => ``LeanInformationAudit.SearchReduction.Failure.missing
        | .isolation => ``LeanInformationAudit.SearchReduction.Failure.isolation
        | .execution => ``LeanInformationAudit.SearchReduction.Failure.execution
        | .heartbeat => ``LeanInformationAudit.SearchReduction.Failure.heartbeat
        | .timeout => ``LeanInformationAudit.SearchReduction.Failure.timeout
        | .cancelled => ``LeanInformationAudit.SearchReduction.Failure.cancelled
        | .undecided => ``LeanInformationAudit.SearchReduction.Failure.undecided)

/-- Only dependencies of checked witness terms are exported, after searching.
Candidate initializers and environment extensions are never executed. -/
private partial def exportConstant (source : Environment) (target n : Name) : MetaM Unit := do
  if n == target then throwError "search.target_in_exported_proof"
  if (← getEnv).contains n then return
  let some info := (source.setExporting false).find? n
    | throwError "search.missing_export_dependency: {n}"
  if (projectionShape info).isSome then
    transportVocabulary {source, target} n
    return
  match info with
  | .thmInfo value =>
    for dep in info.getUsedConstantsAsSet do exportConstant source target dep
    discard <| checkProof n value.levelParams value.type value.value
  | _ => transportVocabulary {source, target} n

/-- The typed result is computed by the same compiled classifier as A1. -/
def publish (name : Name) (r : Observation) (source? : Option Environment := none) : MetaM Unit := do
  unless (r.presentation == .found) == r.presentationEvidence?.isSome do
    throwError "search.presentation_witness_mismatch"
  let baseName := name ++ `baseline
  let pairName := name ++ `paired
  for (n, value) in #[(baseName, runExpr r.base), (pairName, runExpr r.paired),
      (name ++ `presentation, runExpr r.presentation)] do
    addAndCompile (.defnDecl {
      name := n, levelParams := [], type := mkConst ``Run,
      value, hints := .abbrev, safety := .safe })
  addAndCompile (.defnDecl {
    name := name ++ `reason, levelParams := [], type := mkConst ``String,
    value := toExpr r.reason, hints := .abbrev, safety := .safe })
  for (label, value) in #[(`scope, toExpr r.scope), (`configuration, toExpr r.configuration)] do
    addAndCompile (.defnDecl {
      name := name ++ label, levelParams := [],
      type := mkConst ``String, value, hints := .abbrev, safety := .safe})
  for (label, value) in #[(`loadedCount, r.loadedModules.size), (`catalogCount, r.catalogCount)] do
    addAndCompile (.defnDecl {
      name := name ++ label, levelParams := [],
      type := mkConst ``Nat, value := toExpr value, hints := .abbrev, safety := .safe})
  for (label, value) in #[(`loadedModules, toExpr r.loadedModules),
      (`catalogExcluded, toExpr r.catalogExcluded), (`pairedStructureUse, toExpr r.pairedStructureUse),
      (`catalogVerified, toExpr r.catalogVerified)] do
    addAndCompile (.defnDecl {
      name := name ++ label, levelParams := [], type := ← inferType value,
      value, hints := .abbrev, safety := .safe})
  if let some evidence := r.presentationEvidence? then
    addAndCompile (.defnDecl {
      name := name ++ `presentationSource, levelParams := [], type := mkConst ``Name,
      value := toExpr evidence.source, hints := .abbrev, safety := .safe })
    let source := source?.getD (← getEnv)
    let some info := (source.setExporting false).find? r.target
      | throwError "search.missing_presentation_target"
    for dep in info.type.getUsedConstants ++ evidence.conversionType.getUsedConstants ++
        evidence.conversion.getUsedConstants ++ evidence.proof.getUsedConstants do
      exportConstant source r.target dep
    discard <| checkProof (name ++ `presentationConversion) info.levelParams
      evidence.conversionType evidence.conversion
    discard <| checkProof (name ++ `presentationProof) info.levelParams info.type evidence.proof
  let value := mkConst <| match r.verdict with
    | .bindOnly => ``Verdict.bindOnly
    | .nonBindOnly => ``Verdict.nonBindOnly
    | .insufficient => ``Verdict.insufficient
  addAndCompile (.defnDecl {
    name, levelParams := [], type := mkConst ``Verdict,
    value, hints := .abbrev, safety := .safe })
  for (label, rows) in #[(`baselineProof, r.attempts), (`pairedProof, r.pairAttempts)] do
    if let some row := rows.find? (fun row => row.proof?.isSome) then
      if let some proof := row.proof? then
        let source := source?.getD (← getEnv)
        let some info := (source.setExporting false).find? r.target
          | throwError "search.missing_export_target"
        for dep in info.type.getUsedConstants ++ proof.getUsedConstants do
          exportConstant source r.target dep
        discard <| checkProof (name ++ label) info.levelParams info.type proof

syntax (name := referenceBaselineProbeTac) "reference_baseline " ident " at " str
  " baseline " "[" ident,* "]" " from " "[" ident,* "]" : tactic

/-- Only normal exhaustion fails inside the negative guard. An incomplete
replay returns successfully with an error, so `fail_if_success` rejects it
without rolling the diagnostic back as an ordinary tactic exception. -/
@[tactic referenceBaselineProbeTac] unsafe def evalReferenceBaselineProbe : Tactic := fun stx => do
  match stx with
  | `(tactic| reference_baseline $target:ident at $sha:str baseline [$bs:ident,*]
      from [$owners:ident,*]) =>
    profilePhase "imports/source"
    let (source, shared) ← match ← activeProbe.get with
      | some context => pure context
      | none => importSource (owners.getElems.map fun n => {module := n.getId})
    let result ← run source {
      target := target.getId, «baseline» := bs.getElems.map (fun x => x.getId),
      baselineCommit := sha.getString } shared
    if result.presentation == .found then
      evalTactic (← `(tactic| exact True.intro))
      return
    match result.base with
    | .found => evalTactic (← `(tactic| exact True.intro))
    | .exhausted =>
      if let .incomplete failure := result.presentation then
        logError m!"search.presentation_replay_incomplete: {reprStr failure}"
        return
      throwError "search.normal_exhaustion"
    | .incomplete failure =>
      logError m!"search.replay_incomplete: {reprStr failure}: {result.reason}"
      return
  | _ => throwUnsupportedSyntax

syntax (name := searchReductionProbeCmd) "#search_reduction_probe " ident " at " str
  " baseline " "[" ident,* "]" " using " "[" ident,* "]"
  " from " "[" ident,* "]" " as " ident : command

/-- Name ASTs cross the process boundary in a Lean module's binary expression
payload. Numeric segments never pass through identifier syntax or text parsing. -/
private def writeRequest (path : System.FilePath) (request : Request)
    (owners : Array Name) (result : Name) : CommandElabM Unit := do
  let env ← importModules #[{module := `Lean}] options 0
    (leakEnv := true) (loadExts := false)
  let env ← liftTermElabM <| withEnv (env.setMainModule `SearchReductionRequest) do
    for (name, value) in #[(`target, toExpr request.target),
        (`baseline, toExpr request.baseline), (`additions, toExpr request.additions),
        (`owners, toExpr owners), (`result, toExpr result), (`commit, toExpr request.baselineCommit)] do
      let type ← inferType value
      addDecl (.defnDecl {
        name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
    getEnv
  writeModule env path (writeIR := false)

unsafe def executeProbe (request : Request) (owners : Array Name) (name : Name) : CommandElabM Unit := do
  let (source, shared) ← importSource (owners.map fun n => {module := n})
  let result ← run source request shared
  liftTermElabM <| withTheReader Core.Context (fun ctx => {ctx with maxHeartbeats := 0}) do
    if result.verdict == .nonBindOnly then
      -- Construct syntax identifiers directly from the exact Name AST.
      let target := mkIdent request.target
      let sha := Syntax.mkStrLit request.baselineCommit
      let bs := request.baseline.map mkIdent
      let os := owners.map mkIdent
      let guardType := mkConst ``True
      let guardProof ← synthesizeUsingTactic' (u := .zero) guardType (← `(tactic|
          (fail_if_success (reference_baseline $target at $sha baseline [$bs,*] from [$os,*]))
          <;> exact True.intro))
      discard <| checkProof (name ++ `baselineFailureGuard) [] guardType guardProof
    publish name result (some source)
  logInfo (observationJson result request.baselineCommit).compress

/-- Only closed, kernel-checked Name/array/string expression values are read.
No result JSON or source proof is used to construct the request. -/
unsafe def executeProbeFile (path : System.FilePath) : CommandElabM Unit := do
  let (data, region) ← readModuleData path
  probeRegions.modify (·.push region)
  let requestData ← liftTermElabM do
    let getValue := fun name => do
      let some (.defnInfo info) := data.constants.find? (·.name == name)
        | throwError "search.request_data_missing: {name}"
      pure info.value
    let target ← evalExpr Name (mkConst ``Name) (← getValue `target)
    let bs ← evalExpr (Array Name) (mkApp (mkConst ``Array [.zero]) (mkConst ``Name))
      (← getValue `baseline)
    let additions ← evalExpr (Array Name) (mkApp (mkConst ``Array [.zero]) (mkConst ``Name))
      (← getValue `additions)
    let owners ← evalExpr (Array Name) (mkApp (mkConst ``Array [.zero]) (mkConst ``Name))
      (← getValue `owners)
    let name ← evalExpr Name (mkConst ``Name) (← getValue `result)
    let commit ← evalExpr String (mkConst ``String) (← getValue `commit)
    pure ({target, «baseline» := bs, additions, baselineCommit := commit : Request}, owners, name)
  executeProbe requestData.1 requestData.2.1 requestData.2.2

@[command_elab searchReductionProbeCmd] unsafe def elabSearchReductionProbe : CommandElab := fun stx => do
  match stx with
  | `(#search_reduction_probe $target:ident at $sha:str baseline [$bs:ident,*]
      using [$ss:ident,*] from [$owners:ident,*] as $name:ident) =>
    executeProbe {
      target := target.getId, «baseline» := bs.getElems.map (·.getId),
      additions := ss.getElems.map (·.getId), baselineCommit := sha.getString}
      (owners.getElems.map (·.getId)) name.getId
  | _ => throwUnsupportedSyntax

syntax (name := searchReductionCmd) "#search_reduction " ident " at " str
  " baseline " "[" ident,* "]" " using " "[" ident,* "]" " as " ident : command

/-- Separate compiler processes also isolate Mathlib's process-global lazy
indexes. Only compiled Lean declarations are read back; JSON is print-only. -/
@[command_elab searchReductionCmd] unsafe def elabSearchReduction : CommandElab := fun stx => do
  match stx with
  | `(#search_reduction $target:ident at $sha:str baseline [$bs:ident,*] using [$ss:ident,*] as $name:ident) =>
    let source ← getEnv
    for module in bs.getElems do
      unless source.header.moduleNames.contains module.getId do
        let failed : Observation := {
          target := target.getId, base := .incomplete .missing, paired := .incomplete .missing,
          verdict := .insufficient, reason := s!"search.baseline_owner_not_imported: {module.getId}" }
        liftTermElabM <| publish name.getId failed
        logInfo (observationJson failed sha.getString).compress
        return
    let mut modules := #[`LeanInformationAuditRegAnalysis.SearchReduction.Commands] ++
      bs.getElems.map (fun x => x.getId)
    for n in #[target.getId] ++ ss.getElems.map (fun x => x.getId) do
      if n != target.getId && (source.getModuleIdxFor? n).isNone then continue
      let some idx := source.getModuleIdxFor? n
        | let failed : Observation := {
            target := target.getId, base := .incomplete .missing, paired := .incomplete .missing,
            verdict := .insufficient, reason := s!"search.missing_compiled_owner: {n}" }
          liftTermElabM <| publish name.getId failed
          logInfo (observationJson failed sha.getString).compress
          return
      let owner := source.header.moduleNames[idx.toNat]!
      unless modules.contains owner do modules := modules.push owner
    let namePrefix := String.ofList (name.getId.toString.toList.take 48)
    let safeName := (namePrefix.map (fun c => if c.isAlphanum then c else '_')) ++
      s!"_{hash name.getId}"
    let moduleName := "SearchReductionProbe_" ++ safeName
    let directory : System.FilePath := ".lake/build/search-reduction/" ++ safeName ++
      s!"_{← IO.Process.getPID}"
    IO.FS.createDirAll directory
    let directory ← IO.FS.realPath directory
    let input := directory / (moduleName ++ ".lean")
    let output := directory / (moduleName ++ ".olean")
    let imports := String.join ((#[`LeanInformationAuditRegAnalysis.SearchReduction.Commands] ++
      bs.getElems.map (fun n => n.getId)).toList.map fun n => s!"import {n}\n")
    let payload := directory / "request.olean"
    writeRequest payload {
      target := target.getId, «baseline» := bs.getElems.map (·.getId),
      additions := ss.getElems.map (·.getId), baselineCommit := sha.getString} modules name.getId
    let command := s!"run_cmd LeanInformationAudit.SearchReduction.executeProbeFile {repr payload.toString}\n"
    IO.FS.writeFile input (imports ++ command)
    let child ← IO.Process.output {
      cmd := "lean", args := #["-j1", "--root=" ++ directory.toString,
        "-o", output.toString, input.toString]}
    if child.exitCode != 0 then
      if (← IO.getEnv "SEARCH_REDUCTION_VERIFY_INDEX") == some "1" then
        IO.eprintln s!"{child.stdout}\n{child.stderr}"
        IO.Process.exit 1
      let failed : Observation := {
        target := target.getId, base := .incomplete .execution, paired := .incomplete .execution,
        verdict := .insufficient, reason := s!"search.probe_compile_failed: exit {child.exitCode}" }
      liftTermElabM <| publish name.getId failed
      logWarning m!"{child.stdout}\n{child.stderr}"
      logInfo (observationJson failed sha.getString).compress
      return
    logInfo child.stdout
    unless child.stderr.isEmpty do logInfo child.stderr
    let (projected, region) ← readModuleData output
    probeRegions.modify (·.push region)
    liftTermElabM do
      for n in #[name.getId ++ `baseline, name.getId ++ `paired, name.getId ++ `reason,
          name.getId ++ `presentation, name.getId ++ `scope, name.getId ++ `configuration,
          name.getId ++ `loadedCount, name.getId ++ `catalogCount, name.getId ++ `loadedModules,
          name.getId ++ `catalogExcluded, name.getId ++ `pairedStructureUse,
          name.getId ++ `catalogVerified, name.getId ++ `presentationSource,
          name.getId ++ `presentationConversion, name.getId ++ `presentationProof, name.getId,
          name.getId ++ `baselineProof, name.getId ++ `pairedProof,
          name.getId ++ `baselineFailureGuard] do
        match projected.constants.find? (·.name == n) with
        | some (.defnInfo info) => addAndCompile (.defnDecl info)
        | some (.thmInfo info) => discard <| checkProof n info.levelParams info.type info.value
        | _ => pure ()
  | _ => throwUnsupportedSyntax

syntax (name := searchReductionCatalogCmd) "#search_reduction_catalog " str : command
@[command_elab searchReductionCatalogCmd] unsafe def elabSearchReductionCatalog : CommandElab := fun stx => do
  let `(#search_reduction_catalog $sha:str) := stx | throwUnsupportedSyntax
  enableInitializersExecution
  let base ← referenceEnvironment
  let catalog ← baselineCatalog sha.getString #[] base
  logInfo (Json.mkObj [
    ("baseline_commit", toJson sha.getString), ("unit", toJson "frozen-D5-module"),
    ("frozen_modules", toJson (catalog.frozen.map Name.toString)),
    ("B0_count", toJson catalog.eligible.size)]).compress

syntax (name := searchReductionConfigCmd) "#search_reduction_config" : command
@[command_elab searchReductionConfigCmd] unsafe def elabSearchReductionConfig : CommandElab := fun _ => do
  logInfo (Json.mkObj [("version", toJson "R_loc"), ("maxHeartbeats", toJson localBudget),
    ("transport", toJson transportVersion), ("reconstructionMaxHeartbeats", toJson reconstructionBudget),
    ("reconstructionBudgetSemantics", toJson "independent_units"),
    ("pinnedDeriving", toJson (pinnedDerivingClasses.map Name.toString)),
    ("configuration", toJson "R_loc/hidden-data-k2/200000"),
    ("lean", toJson Lean.versionString), ("mathlib", toJson mathlibRevision),
    ("k", toJson (2 : Nat)), ("graphCapacity", toJson graphCapacity),
    ("strategies", toJson (["intro", "assumption", "rfl", "And/Iff/Exists/Subtype", "ordered-apply-depth2", "simp-only-direct-eq-iff/no-simprocs", "omega/no-mvars"] : List String))]).compress

end LeanInformationAudit.SearchReduction
