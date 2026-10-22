import LeanInformationAuditRegAnalysis.SearchReduction.Vocabulary
import LeanInformationAuditRegAnalysis.SearchReduction.Catalog

/-! Compiled-environment isolation and immutable baseline provenance. -/

namespace LeanInformationAudit.SearchReduction
open Lean Meta
open LeanInformationAudit.SearchReduction (classifyCertified Failure)

/-- The source environment is used only to recover types and check compiled
values. Probe environments start from independent baseline imports. -/
structure Request where
  target : Name
  baseline : Array Name
  additions : Array Name := #[]
  baselineCommit : String
  informationApplication : Option Name := none
  deriving Inhabited

private def sourceInfo (source : Environment) (n : Name) : MetaM ConstantInfo :=
  match (source.setExporting false).find? n with
  | some info => pure info
  | none => throwError "search.missing_declaration: {n}"

private def checkedSource (source : Environment) (n : Name) : MetaM ConstantInfo := do
  let info ← sourceInfo source n
  let xs ← withEnv source (collectAxioms n)
  unless standardAxioms xs do throwError "search.axioms_outside_standard: {n}: {xs}"
  return info

/-- S may not contain T, its supported full-statement aliases, or a dependency
on either. Conjunction packaging is inspected before the structure is copied. -/
partial def copyStructure (source : Environment) (target : Name) (targetType : Expr)
    (n : Name) (index : FactIndex) (visiting : NameSet := {}) : MetaM Unit := do
  if n == target then throwError "search.target_leak: {n}"
  if visiting.contains n then return
  let info ← checkedSource source n
  -- Recover only vocabulary needed by the statement. Certificate elaboration
  -- stays in B's environment, including its registered tactic implementations.
  -- The detached source environment supplies no extension state or proofs.
  let type ← copyStatement source n info.type
  if (← singleSourceConversion targetType type).isSome ||
      (← certifiedRestatement targetType type index) then
    throwError "search.target_restatement: {n}"
  if (← getEnv).contains n then return
  for dep in info.getUsedConstantsAsSet do
    if (← getEnv).contains dep then continue
    let depInfo ← sourceInfo source dep
    if ← withEnv source (isProp depInfo.type) then
      copyStructure source target targetType dep index (visiting.insert n)
    else
      throwError "search.structure_vocabulary_not_reconstructed: {dep}"
  match info with
  | .thmInfo value => addDecl (.thmDecl {value with type})
  | .defnInfo value => addDecl (.defnDecl {value with type})
  | _ => throwError "search.unsupported_structure_kind: {n}"

/-- The finite union guard uses abstract S assumptions and their projections.
It does not invoke R or arbitrary derivability. The old per-member conversion
remains an independent disjunct in copyStructure. -/
def collectionLeak (target : Expr) (types : Array Expr) : MetaM Bool := do
  let saved ← saveState
  let result ← forallTelescope target fun xs body => do
    let mut aligned := #[]
    for type in types do
      let mut current := type
      let mut compatible := true
      for x in xs do
        let .forallE _ domain rest kind := current | compatible := false; break
        if kind != (← getFVarLocalDecl x).binderInfo then
          compatible := false
          break
        unless ← withReducible <| isDefEq domain (← inferType x) do
          compatible := false
          break
        current := rest.instantiate1 x
      if compatible && !current.isForall then aligned := aligned.push current
    if aligned.isEmpty then return false
    let mut combined := aligned[0]!
    for type in aligned[1:] do combined ← mkAppM ``And #[combined, type]
    if let some conversion ← singleSourceConversion body combined then
      let conversion ← mkLambdaFVars xs conversion
      let type ← inferType conversion
      let levels := (collectLevelParams {} type).params.toList
      discard <| checkProof (← mkFreshUserName `_collectionLeak) levels type conversion
      return true
    return false
  saved.restore
  return result

private partial def structureTypes (source : Environment) (n : Name)
    (seen : NameSet := {}) : MetaM (Array Expr) := do
  if seen.contains n || (← getEnv).contains n then return #[]
  let info ← checkedSource source n
  let mut result := #[← copyStatement source n info.type]
  for dep in info.getUsedConstantsAsSet do
    if (← getEnv).contains dep then continue
    let depInfo ← sourceInfo source dep
    if ← withEnv source (isProp depInfo.type) then
      result := result ++ (← structureTypes source dep (seen.insert n))
  return result

/-- Rebuild proof dependencies' computational vocabulary before installing any
S certificate. Side proofs remain checked payloads in the common prefix. -/
private partial def structureVocabulary (ctx : TransportContext) (n : Name)
    (seen : NameSet := {}) : MetaM Unit := do
  if seen.contains n || (← getEnv).contains n then return
  if ctx.forbidden.contains n && n == ctx.target then
    throwError "search.target_leak: {n}"
  let info ← checkedSource ctx.source n
  if ← withEnv ctx.source (isProp info.type) then
    for dep in info.getUsedConstantsAsSet do
      structureVocabulary ctx dep (seen.insert n)
  else
    transportVocabulary ctx n

private def checkVocabularyClean (source base : Environment) (regenerated : NameSet := {}) : MetaM Unit := do
  let localNames := (← getEnv).constants.foldStage2 (fun names n _ => names.push n) (#[] : Array Name)
  for n in localNames do
    if base.contains n || regenerated.contains n then continue
    if let some info := (source.setExporting false).find? n then
      -- A regenerated projection is a logical accessor, not an author body.
      if (projectionShape info).isSome then continue
      -- Kernel-rebuilt logical constructors and eliminators are vocabulary.
      match info with
      | .inductInfo _ | .ctorInfo _ | .recInfo _ => continue
      | _ => pure ()
      if ← withEnv source (isProp info.type) then
        throwError "search.author_proof_in_common_vocabulary: {n}"

/-- Presentation units account for and report their own work. Only that work
is excluded from the enclosing isolation allocation; all other isolation work
retains the original cumulative command limit. -/
private def prepareAdditions (source base : Environment) (index : FactIndex) :
    List Name → Array Expr → MetaM (Array Expr × Nat)
  | [], types => pure (types, 0)
  | n :: rest, types => do
    if compilerGenerated source n || (← withEnv source <| isEqnThm n) then
      IO.eprintln s!"structure member: source={n}, disposition=folded-compiler-auxiliary"
      return ← prepareAdditions source base index rest types
    if base.contains n then throwError "search.structure_already_in_baseline: {n}"
    let info ← checkedSource source n
    let type ← copyStatement source n info.type
    let started ← IO.getNumHeartbeats
    let (present, evidence?, detail) ← baselinePresentation (← getEnv) info.levelParams type (some index)
      (requireNonneutral := true)
    let used := (← IO.getNumHeartbeats) - started
    IO.eprintln s!"structure presentation: source={n}, independent_heartbeats={used}, {detail}"
    withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := ctx.initHeartbeats + used}) do
      if present == .found then
        throwError "search.structure_baseline_presentation: {n}: source={evidence?.map (·.source)}"
      if let .incomplete _ := present then throwError "search.structure_presentation_incomplete: {n}"
      let types := types ++ (← structureTypes source n)
      let (types, remainingUsed) ← prepareAdditions source base index rest types
      return (types, used + remainingUsed)

private def prepare (source base : Environment) (request : Request)
    (paired : Bool) : IO (Except (Failure × String) (Environment × ConstantInfo × Option Attempt)) := do
  let work : CoreM (Environment × ConstantInfo × Option Attempt) := MetaM.run' do
    let target ← checkedSource source request.target
    unless ← withEnv source (isProp target.type) do
      throwError "search.target_not_proposition: {request.target}"
    let forbidden := request.additions.foldl (fun ns n => ns.insert n) (({} : NameSet).insert request.target)
    let regenerated ← IO.mkRef ({} : NameSet)
    let searchHeartbeats ← IO.mkRef 0
    let budgetStart ← IO.getNumHeartbeats
    let transport : TransportContext := {
      source, target := request.target, targetType := target.type, forbidden,
      regenerated? := some regenerated, budgetStart, searchHeartbeats? := some searchHeartbeats}
    let mut roots := target.type.getUsedConstants
    for n in request.additions do
      if let some info := (source.setExporting false).find? n then
        roots := roots ++ info.type.getUsedConstants
    let preflightStart ← IO.getNumHeartbeats
    vocabularyBudgetPreflight source roots
    let preflightUsed := (← IO.getNumHeartbeats) - preflightStart
    let type ← transportStatement transport request.target target.type
    let target := match target with
      | .thmInfo value => ConstantInfo.thmInfo {value with type}
      | .defnInfo value => ConstantInfo.defnInfo {value with type}
      | other => other
    -- Both arms receive exactly the vocabulary of T and all registered S types.
    for n in request.additions do
      if let some info := (source.setExporting false).find? n then
        discard <| transportStatement transport n info.type
    checkTargetVocabularyProjections source base target.type
    checkVocabularyClean source base (← regenerated.get)
    let accounted ← searchHeartbeats.get
    let excluded := preflightUsed + accounted
    withTheReader Core.Context (fun reader =>
        {reader with initHeartbeats := reader.initHeartbeats + excluded}) do
      if paired then
        let index ← factIndex
        let (types, used) ← prepareAdditions source base index request.additions.toList #[]
        -- Continue with the same allocation consumed by nonpresentation work.
        -- prepareAdditions adjusts only its recursive continuation's reader.
        withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := ctx.initHeartbeats + used}) do
          for type in types do
            discard <| transportStatement transport request.target type
          for n in request.additions do structureVocabulary transport n
          checkVocabularyClean source base (← regenerated.get)
          let extraSearch := (← searchHeartbeats.get) - accounted
          withTheReader Core.Context (fun ctx =>
              {ctx with initHeartbeats := ctx.initHeartbeats + extraSearch}) do
            if ← collectionLeak target.type types then throwError "search.structure_collection_restatement"
            for n in request.additions do
              copyStructure source request.target target.type n index
      return (← getEnv, target, none)
  try
    let context : Core.Context := {
      fileName := "<R_v1 isolation>", fileMap := default, options := options,
      initHeartbeats := ← IO.getNumHeartbeats, maxHeartbeats := reconstructionBudget * 1000 }
    match ← (work.run context {env := base}).toIO' with
    | .ok (value, state) =>
      if state.messages.hasErrors then return .error (.execution, "search.isolation_errors")
      return .ok value
    | .error ex =>
      let failure := if ex.isMaxHeartbeat then Failure.heartbeat
        else if ex.isInterrupt then .cancelled
        else if ex.isRuntime then .execution else .isolation
      return .error (failure, ← ex.toMessageData.toString)
  catch ex => return .error (.execution, ex.toString)

/-- Provenance uses source identity, never program size as a reuse criterion.
Every repository module imported by B must match the registered commit; D5
members must already have frozen membership at that commit. -/
def checkBaseline (request : Request) (base : Environment) : IO (Except String Unit) := do
  unless Lean.versionString == "4.35.0" do return .error "search.lean_pin_mismatch"
  let mathlib ← IO.Process.output {
    cmd := "git", args := #["-C", ".lake/packages/mathlib", "rev-parse", "HEAD"] }
  unless mathlib.exitCode == 0 && mathlib.stdout.trimAscii.toString == mathlibRevision do
    return .error "search.mathlib_pin_mismatch"
  if request.baselineCommit.length != 40 ||
      !request.baselineCommit.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    return .error "search.missing_immutable_baseline"
  let commit ← IO.Process.output {
    cmd := "git", args := #["cat-file", "-e", request.baselineCommit ++ "^{commit}"] }
  if commit.exitCode != 0 then return .error "search.baseline_commit_missing"
  for path in #["lean-toolchain", "lake-manifest.json"] do
    let old ← IO.Process.output {
      cmd := "git", args := #["show", s!"{request.baselineCommit}:{path}"] }
    unless old.exitCode == 0 && old.stdout == (← IO.FS.readFile path) do
      return .error s!"search.baseline_dependency_pin_mismatch: {path}"
  for module in base.header.moduleNames do
    let path := module.toString.replace "." "/" ++ ".lean"
    if module.toString.startsWith "D5." then
      let old ← IO.Process.output {cmd := "git", args := #["show", s!"{request.baselineCommit}:{path}"]}
      if old.exitCode != 0 then return .error s!"search.baseline_source_missing: {module}"
      unless old.stdout == (← IO.FS.readFile path) do
        return .error s!"search.baseline_source_mismatch: {module}"
      let frozen ← IO.Process.output {cmd := "git", args := #["cat-file", "-e",
        s!"{request.baselineCommit}:Golden/Frozen/state/{path}.json"]}
      if frozen.exitCode != 0 then return .error s!"search.baseline_not_frozen: {module}"
    else if !(module.toString.startsWith "Init" || (module.toString == "Lean" || module.toString.startsWith "Lean.") ||
        module.toString == "Lake" || module.toString.startsWith "Lake." ||
        module.toString.startsWith "Std" || module.toString.startsWith "Mathlib" ||
        module.toString.startsWith "Batteries" || module.toString.startsWith "Aesop" ||
        module.toString.startsWith "Qq" || module.toString.startsWith "Plausible" ||
        module.toString.startsWith "LeanSearchClient" ||
        module.toString.startsWith "ImportGraph" || module.toString.startsWith "ProofWidgets") then
      -- Test baselines use the same immutable source check, without pretending
      -- that a synthetic fixture is a frozen mathematical module.
      let fixture := "tools/lean-inspector/" ++ path
      let old ← IO.Process.output {cmd := "git", args := #["show", s!"{request.baselineCommit}:{fixture}"]}
      if old.exitCode != 0 then return .error s!"search.baseline_module_unregistered: {module}"
      unless old.stdout == (← IO.FS.readFile fixture) do
        return .error s!"search.baseline_source_mismatch: {module}"
  return .ok ()

private def intervalRun (graph : ProofGraph) (interval : Interval) : Run :=
  if upperIsZero interval then .found
  else if graph.complete && graph.edges.all (fun e => e.window != 1 || e.cost != .unknown) &&
      finite interval.lower && finite interval.upper then .exhausted
  else .incomplete .undecided

/-- Meta caches can retain imported names, levels and types after a branch
restores its environment. Their compacted storage lives until process exit. -/
private initialize candidateRegions : IO.Ref (Array CompactedRegion) ← IO.mkRef #[]

/-- Temporary vocabulary belongs to the candidate branch. Only a successful
certificate is inlined and checked against the original query environment. -/
unsafe def onDemandLookup (table : LookupTable)
    (sharedImports? : Option ImportState := none) : IO LookupTable := do
  let cache ← IO.mkRef (none : Option (String × Environment))
  let verified ← IO.mkRef false
  let retained := if sharedImports?.isSome then
      table.environment.header.regions.foldl (fun names region =>
        names.insert region.filePath.toString) ({} : Std.HashSet String)
    else {}
  let close : IO Unit := do
    cache.set none
  let acquire (module : Name) (options : Options) : IO Environment := withImporting do
    lookupPhase s!"candidate/import-start module={module}"
    let imports : Array Import := #[{module}]
    let (_, state) ← (importModulesCore imports).run (sharedImports?.getD default)
    let env ← finalizeImport state imports options 0 (leakEnv := false) (loadExts := false)
    let regions := env.header.regions.filter fun region =>
      !retained.contains region.filePath.toString
    candidateRegions.modify (· ++ regions)
    lookupPhase s!"candidate/regions-retained count={regions.size} total={(← candidateRegions.get).size}"
    lookupPhase s!"candidate/import-end module={module}"
    return env
  let finish (base : Environment) (proof : Expr) : MetaM Expr := do
    let proof ← inlineLookupSupport base proof
    return detachLookupExpression proof
  return {table with
    close? := some close
    finish? := some finish
    load? := some fun entry head => do
      let started ← IO.monoMsNow
      let context ← readThe Core.Context
      if entry.module.startsWith "D5." && !(← verified.get) then
        let some disk := table.disk? | throwError "lookup.candidate_without_snapshot"
        let check ← IO.Process.output {
          cmd := "git"
          args := #["diff", "--quiet", disk.header.basis, "--", "D5"]}
        unless check.exitCode == 0 do throwError "lookup.candidate_snapshot_changed"
        verified.set true
      let ready ← cache.get
      let source ← if let some (name, source) := ready then
          if name == entry.module then pure source else do
            close
            let source ← acquire entry.module.toName context.options
            cache.set (some (entry.module, source))
            pure source
        else do
          let source ← acquire entry.module.toName context.options
          cache.set (some (entry.module, source))
          pure source
      let result ← timeLookup s!"candidate/copy name={entry.name}" <| copyLookupCandidateWith (fun source proof =>
        copyCertificateExpression {source, enclosingBudget := true} proof) source entry head
      if (← IO.getEnv "SEARCH_REDUCTION_PROFILE").isSome then
        IO.eprintln s!"LOOKUP_COST candidate_import_copy_ms={(← IO.monoMsNow) - started} module={entry.module}"
      checkSystem "lookup.candidate_import"
      let (proofs, params, failures) := result
      let levels ← params.mapM fun _ => mkFreshLevelMVar
      return (proofs.map (·.instantiateLevelParams params levels), failures)}

private unsafe def runCore (source base : Environment) (request : Request)
    (lookupComplete : Bool) (disk? : Option DiskLookup.Index := none)
    (sharedImports? : Option ImportState := none) : IO Observation := do
  let unknown (reason : String) (failure := Failure.isolation) : Observation := {
    target := request.target, base := .incomplete failure,
    paired := .incomplete failure, verdict := .insufficient, reason}
  try
    unless source.contains request.target do return unknown "search.missing_target" .missing
    if let .error reason ← checkBaseline request base then return unknown reason
    profilePhase "query/prepare-start"
    let prepared ← prepare source base request false
    let .ok (clean, target, _) := prepared
      | let (failure, reason) := match prepared with
          | .error failure => failure | _ => (.isolation, "search.isolation_failed")
        return unknown reason failure
    if clean.contains request.target then return unknown "search.target_already_in_baseline"
    let presentationIndex : FactIndex := {
      environment? := some clean
      enumerationSize := clean.constants.fold (fun count _ _ => count + 1) 0}
    profilePhase "query/presentation-start"
    let (presentation, presentationEvidence?, presentationDetail) ←
      baselinePresentation clean target.levelParams target.type (some presentationIndex)
    profilePhase "query/structure-start"
    let mut pairedEnv := clean
    let mut structureChecked := false
    let mut structureReason := ""
    let mut structureFailure : Option Failure := none
    if !request.additions.isEmpty then
      match ← prepare source clean request true with
      | .ok (env, _, _) => pairedEnv := env; structureChecked := true
      | .error (failure, reason) =>
        structureReason := reason
        structureFailure := some failure
    let work : CoreM Observation := MetaM.run' do
      profilePhase "query/extraction-start"
      let added := if structureChecked then request.additions else #[]
      let graph ← withEnv source <| extractGraph base request.target added
      let vertices ← graph.vertices.mapM fun v => do
        return {v with type := ← copyStatement source (v.origin.constName?.getD .anonymous) v.type}
      let graph := {graph with vertices}
      let graphEnv ← getEnv
      let enabled := (← IO.getEnv "SEARCH_REDUCTION_LOOKUP") != some "0"
      profilePhase "query/evaluation-start"
      let table ← onDemandLookup {
        environment := base, complete := lookupComplete, enabled, disk?} sharedImports?
      let reading ← withEnv graphEnv <| evaluateGraph graph (some table)
      profilePhase "query/assembly-start"
      let baselineProof? ← if upperIsZero reading.baseline then
        withEnv graphEnv <| assembleZero reading.graph else pure none
      let pairedProof? ← if upperIsZero reading.paired then
        withEnv pairedEnv do
          for v in graph.vertices do
            discard <| copyStatement source (v.origin.constName?.getD .anonymous) v.type
          assembleZero reading.graph true
        else pure none
      let reading := {reading with
        baseline := if upperIsZero reading.baseline && baselineProof?.isNone then
          {reading.baseline with upper := .top} else reading.baseline
        paired := if upperIsZero reading.paired && pairedProof?.isNone then
          {reading.paired with upper := .top} else reading.paired
        baselineProof?, pairedProof?, isolated := true, structureChecked,
        structureClean := structureChecked, presentationCertified := presentation == .found,
        presentationComplete := match presentation with | .incomplete _ => false | _ => true}
      let baseRun := intervalRun reading.graph reading.baseline
      let pairedGraph := {reading.graph with edges := reading.graph.edges.map (fun edge => {edge with cost := edge.pairedCost})}
      let pairRun := match structureFailure with
        | some failure => .incomplete failure
        | none => intervalRun pairedGraph reading.paired
      let attempts := baselineProof?.toArray.map fun proof =>
        {strategy := "graph/assembled-zero", outcome := .found, proof? := some proof : Attempt}
      let pairAttempts := pairedProof?.toArray.map fun proof =>
        {strategy := "graph/assembled-zero", outcome := .found, proof? := some proof : Attempt}
      return {
        target := request.target, base := baseRun, paired := pairRun,
        verdict := classifyGraph reading, attempts, pairAttempts,
        targetChecked := true, structureChecked, structureClean := structureChecked,
        presentation, presentationEvidence?, presentationDetail, graph? := some reading,
        reason := structureReason}
    let context : Core.Context := {
      fileName := "<proof graph>", fileMap := default,
      options := options.set `maxHeartbeats 0,
      initHeartbeats := ← IO.getNumHeartbeats, maxHeartbeats := 0}
    match ← (work.run context {env := clean}).toIO' with
    | .ok (result, state) =>
      if state.messages.hasErrors then return unknown "graph.elaboration_errors" .execution
      return result
    | .error ex => return unknown (← ex.toMessageData.toString) .execution
  catch ex => return unknown s!"search.execution:{ex}" .execution

/-- Fork only immutable module storage. Candidate extensions are never merged
into the baseline environment used for local reconstruction. -/
unsafe def run (source : Environment) (request : Request)
    (sharedImports : ImportState := default) : IO Observation := do
  unless source.contains request.target do
    return {
      target := request.target, verdict := .insufficient, base := .incomplete .missing,
      paired := .incomplete .missing, reason := "search.missing_target"}
  try
    enableInitializersExecution
    let imports : Array Import := #[{module := `Mathlib}] ++
      request.baseline.map (fun n => {module := n})
    profilePhase "query/base-import-start"
    let (base, baseImports) ← withImporting do
      let (_, state) ← (importModulesCore imports).run sharedImports
      let base ← finalizeImport state imports options 0 (leakEnv := false) (loadExts := true)
      pure (base, state)
    profilePhase "query/base-import-end"
    let mut delivery := #[]
    for n in #[request.target] ++ request.additions do
      if let some index := source.getModuleIdxFor? n then
        delivery := delivery.push source.header.moduleNames[index.toNat]!
    let catalog ← baselineCatalog request.baselineCommit delivery base
    let directory := (← IO.getEnv "SEARCH_REDUCTION_INDEX").getD
      s!"build/lean-inspector/lookup-index/{request.baselineCommit}"
    let disk? ← try
      pure (some (← DiskLookup.openIndex directory request.baselineCommit mathlibRevision catalog.excluded))
      catch _ => pure none
    let result ← runCore source base request disk?.isSome disk? (some baseImports)
    let used := request.additions.filter fun name =>
      result.graph?.any fun reading => reading.selectedSeeds.any fun id =>
        reading.graph.vertices.any fun vertex => vertex.id == id &&
          vertex.structureProof?.any (fun proof => proof.getUsedConstants.contains name)
    return {result with
      catalogCount := catalog.eligible.size, loadedModules := catalog.loaded,
      catalogExcluded := catalog.excluded, scope := "B_used/" ++ catalog.scope,
      catalogVerified := true, pairedStructureUse := used}
  catch ex =>
    return {
      target := request.target, verdict := .insufficient, base := .incomplete .isolation,
      paired := .incomplete .isolation, presentation := .incomplete .isolation,
      reason := s!"search.catalog_incomplete:{ex}"}

end LeanInformationAudit.SearchReduction
