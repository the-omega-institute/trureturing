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
  certificates : Array CertificateNomination := #[]
  edgeCertificates : Array (Name × CertificateNomination) := #[]
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

initialize isolationUnitReadings : IO.Ref (Array Json) ← IO.mkRef #[]
initialize isolationUnitCount : IO.Ref Nat ← IO.mkRef 0
initialize isolationRejection : IO.Ref (Option String) ← IO.mkRef none

/-- The immutable, deduplicated check domain includes transitive proof
dependencies absent from the reconstructed prefix. -/
private partial def restatementDomain (source base : Environment) (pending : List Name)
    (seen : NameSet := {}) : MetaM NameSet := do
  match pending with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then
      return ← restatementDomain source base rest seen
    let info ← checkedSource source n
    if let .ctorInfo _ := info then
      if base.contains n then return ← restatementDomain source base rest seen
    let mut dependencies := rest
    unless base.contains n do
      for dep in info.getUsedConstantsAsSet do
        unless base.contains dep do
          let depInfo ← sourceInfo source dep
          if ← withEnv source (isProp depInfo.type) then
            dependencies := dep :: dependencies
    restatementDomain source base dependencies (seen.insert n)

/-- The production per-check boundary, including durable named fault readings.
Recursive work inside the action shares this allocation. -/
def withRestatementUnit (target n : Name) (phase : IO.Ref String)
    (action : MetaM Unit) : MetaM Nat := do
  let started ← IO.getNumHeartbeats
  let record (status : String) : MetaM Unit := do
    let used := (← IO.getNumHeartbeats) - started
    let row := Json.mkObj [
      ("target", toJson target.toString), ("source", toJson n.toString),
      ("guard", toJson "single-source-and-legacy-restatement"),
      ("status", toJson status), ("internal_heartbeats", toJson used),
      ("external_heartbeats", toJson (used / 1000)),
      ("limit_external", toJson reconstructionBudget)]
    isolationUnitReadings.modify (·.push row)
    IO.eprintln s!"ISOLATION_CHECK_UNIT {row.compress}"
  catchLookupCandidate
    (withTheReader Core.Context (fun ctx => {ctx with
        initHeartbeats := started, maxHeartbeats := reconstructionBudget * 1000}) do
      phase.set s!"restatement-unit:{target}:{n}:single-source-and-legacy"
      action
      checkSystem "isolation.restatement-unit"
      record "complete")
    (fun ex => do
      let rejection ← isolationRejection.get
      record (if ex.isMaxHeartbeat then "incomplete:unit-heartbeat"
        else if rejection.isSome then "reject" else "fault")
      throw ex)
  return (← IO.getNumHeartbeats) - started

/-- One complete single-source plus legacy check owns one allocation. All
recursive legacy calls share it; only the enclosing continuation excludes it. -/
private def checkRestatementUnits (source : Environment) (target : Name)
    (targetType : Expr) (index : FactIndex) (normalization : IO.Ref LegacyNormalizationMemo)
    (phase : IO.Ref String) : List Name → MetaM Nat
  | [] => pure 0
  | n :: rest => do
    let used ← withRestatementUnit target n phase do
      let info ← checkedSource source n
      let type ← copyStatement source n info.type
      let single := (← singleSourceConversion targetType type).isSome
      if single || (← certifiedRestatement targetType type index (some normalization)) then
        isolationRejection.set (some s!"single-source-and-legacy-restatement:{target}:{n}")
        throwError "search.target_restatement: {n}"
    withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := ctx.initHeartbeats + used}) do
      return used + (← checkRestatementUnits source target targetType index normalization phase rest)

/-- S may not contain T, its supported full-statement aliases, or a dependency
on either. Conjunction packaging is inspected before the structure is copied. -/
partial def copyStructure (source : Environment) (target : Name) (targetType : Expr)
    (n : Name) (index : FactIndex) (visiting : NameSet := {})
    (phase? : Option (IO.Ref String) := none)
    (normalization? : Option (IO.Ref LegacyNormalizationMemo) := none)
    (checked? : Option NameSet := none) : MetaM Unit := do
  let mark := fun step => phase?.mapM fun phase => phase.set s!"structure-copy:{n}:{step}"
  discard <| mark "source-check"
  if n == target then
    isolationRejection.set (some s!"source-isolation:{target}:{n}")
    throwError "search.target_leak: {n}"
  if visiting.contains n then return
  let info ← checkedSource source n
  -- A kernel-rebuilt constructor is common vocabulary, never an added fact.
  if let .ctorInfo _ := info then
    if (← getEnv).contains n then return
  -- Recover only vocabulary needed by the statement. Certificate elaboration
  -- stays in B's environment, including its registered tactic implementations.
  -- The detached source environment supplies no extension state or proofs.
  discard <| mark "statement"
  let type ← copyStatement source n info.type
  discard <| mark "single-source"
  unless checked?.any (·.contains n) do
    let single := (← singleSourceConversion targetType type).isSome
    discard <| mark "legacy-restatement"
    if single || (← certifiedRestatement targetType type index normalization?) then
      throwError "search.target_restatement: {n}"
  if (← getEnv).contains n then return
  discard <| mark "dependencies"
  for dep in info.getUsedConstantsAsSet do
    if (← getEnv).contains dep then continue
    let depInfo ← sourceInfo source dep
    if ← withEnv source (isProp depInfo.type) then
      copyStructure source target targetType dep index (visiting.insert n) phase? normalization? checked?
    else
      throwError "search.structure_vocabulary_not_reconstructed: {dep}"
  discard <| mark "kernel-install"
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
    if let .ctorInfo _ := info then
      if (← getEnv).contains n then
        IO.eprintln s!"structure member: source={n}, disposition=common-vocabulary-constructor"
        return ← prepareAdditions source base index rest types
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

/-- The operation pair and actual stop survive every isolation exception. -/
def isolationFailure (ex : Exception) (paired : Bool) (stage : String) : IO (Failure × String) := do
  let failure := if ex.isMaxHeartbeat then Failure.heartbeat
    else if ex.isInterrupt then .cancelled
    else if ex.isRuntime then .execution else .isolation
  let arm := if paired then "paired" else "baseline"
  let detail ← ex.toMessageData.toString
  let reason := if ex.isMaxHeartbeat then
      s!"search.isolation_reconstruction_heartbeat: arm={arm};stage={stage};\
        limit={reconstructionBudget};{detail}"
    else s!"{detail};isolation_arm={arm};isolation_stage={stage}"
  return (failure, reason)

/-- Reconstruct one arm without running or pricing any graph query. -/
def prepare (source base : Environment) (request : Request)
    (paired : Bool) (originalBaseline? : Option Environment := none) : IO (Except (Failure × String) (Environment × ConstantInfo × Option Attempt)) := do
  let phase ← IO.mkRef "source-check"
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
    phase.set "vocabulary-preflight"
    vocabularyBudgetPreflight source roots
    let preflightUsed := (← IO.getNumHeartbeats) - preflightStart
    phase.set "target-vocabulary"
    let type ← transportStatement transport request.target target.type
    let target := match target with
      | .thmInfo value => ConstantInfo.thmInfo {value with type}
      | .defnInfo value => ConstantInfo.defnInfo {value with type}
      | other => other
    -- Both arms receive exactly the vocabulary of T and all registered S types.
    for n in request.additions do
      phase.set s!"structure-statement:{n}"
      if let some info := (source.setExporting false).find? n then
        discard <| transportStatement transport n info.type
    phase.set "vocabulary-cleanliness"
    checkTargetVocabularyProjections source base target.type
    checkVocabularyClean source base (← regenerated.get)
    let accounted ← searchHeartbeats.get
    let excluded := preflightUsed + accounted
    withTheReader Core.Context (fun reader =>
        {reader with initHeartbeats := reader.initHeartbeats + excluded}) do
      if paired then
        let index ← factIndex
        phase.set "structure-presentation"
        let (types, used) ← prepareAdditions source (originalBaseline?.getD base) index request.additions.toList #[]
        -- Continue with the same allocation consumed by nonpresentation work.
        -- prepareAdditions adjusts only its recursive continuation's reader.
        withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := ctx.initHeartbeats + used}) do
          for type in types do
            phase.set "structure-type-transport"
            discard <| transportStatement transport request.target type
          for n in request.additions do
            phase.set s!"structure-vocabulary:{n}"
            structureVocabulary transport n
          phase.set "structure-vocabulary-cleanliness"
          checkVocabularyClean source base (← regenerated.get)
          let extraSearch := (← searchHeartbeats.get) - accounted
          withTheReader Core.Context (fun ctx =>
              {ctx with initHeartbeats := ctx.initHeartbeats + extraSearch}) do
            phase.set "collection-leak"
            if ← collectionLeak target.type types then
              isolationRejection.set (some s!"collection-restatement:{request.target}")
              throwError "search.structure_collection_restatement"
            let normalization ← IO.mkRef ({} : LegacyNormalizationMemo)
            let domain ← restatementDomain source (← getEnv) request.additions.toList
            let units := domain.toArray.qsort (fun a b => a.toString < b.toString)
            isolationUnitCount.set units.size
            IO.eprintln s!"ISOLATION_CHECK_BUDGET m={units.size} unit_external={reconstructionBudget} original_external={reconstructionBudget} total_external={(units.size + 1) * reconstructionBudget} internal_per_external=1000"
            let used ← checkRestatementUnits source request.target target.type index normalization phase units.toList
            withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := ctx.initHeartbeats + used}) do
              for n in request.additions do
                phase.set s!"structure-copy:{n}"
                copyStructure source request.target target.type n index (phase? := some phase)
                  (normalization? := some normalization) (checked? := some domain)
            let normalization ← normalization.get
            IO.eprintln s!"legacy normalization: hits={normalization.hits}, misses={normalization.misses}"
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
      return .error (← isolationFailure ex paired (← phase.get))
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
  else if graph.complete && strictDrop interval ⟨.finite 0, .finite 0⟩ then .exhausted
  else .incomplete .undecided

/-- Checked certificates may share expression storage with their imported
module even after reconstruction. Keep their backing regions for this compiler
lifetime, like checkpoint and query-cache certificate regions. -/
private initialize certificateRegions : IO.Ref (Array CompactedRegion) ← IO.mkRef #[]

/-- Temporary environments are bounded to one module. A failed candidate
restores its Meta/Core state before another module can replace the source.
The branch boundary restores state before close releases unsuccessful storage;
exported certificates retain their backing regions through compiler exit. -/
unsafe def onDemandLookup (table : LookupTable)
    (sharedImports? : Option ImportState := none) : IO LookupTable := do
  let cache ← IO.mkRef (none : Option (String × Options × Environment))
  let regions ← IO.mkRef (#[] : Array CompactedRegion)
  let certificateEscaped ← IO.mkRef false
  let memo ← IO.mkRef ({} : LookupQueryMemo)
  let verified ← IO.mkRef false
  let budget ← IO.mkRef ({} : LookupBudgetState)
  let retained := if sharedImports?.isSome then
      table.environment.header.regions.foldl (fun names region =>
        names.insert region.filePath.toString) ({} : Std.HashSet String)
    else {}
  let close : IO Unit := do
    cache.set none
    let releasing ← regions.get
    regions.set #[]
    if ← certificateEscaped.get then
      certificateRegions.modify (· ++ releasing)
    else
      for region in releasing.reverse do region.free
    certificateEscaped.set false
  let acquire (module : Name) (options : Options) : IO Environment := withImporting do
    close
    lookupPhase s!"candidate/import-start module={module}"
    let imports : Array Import := table.environment.header.imports.push {module}
    let (_, state) ← (importModulesCore imports).run (sharedImports?.getD default)
    let env ← finalizeImport state imports options 0 (leakEnv := false) (loadExts := false)
    let owned := env.header.regions.filter fun region =>
      !retained.contains region.filePath.toString
    regions.set owned
    lookupPhase s!"candidate/regions-bounded count={owned.size} modules=1"
    lookupPhase s!"candidate/import-end module={module}"
    cache.set (some (module.toString, options, env))
    return env
  let finish (base : Environment) (proof : Expr) : MetaM Expr := do
    -- Reduce the selected view before inspecting its support. Discarded
    -- conjunction/subtype fields need not belong to the query vocabulary.
    let proof ← Meta.transform proof (post := fun e => do
      if let some name := e.getAppFn.constName? then
        if let some info := (← getEnv).getProjectionFnInfo? name then
          let args := e.getAppArgs
          if info.numParams < args.size then
            if let some value ← project? args[info.numParams]! info.i then
              return .visit (mkAppN value (args.extract (info.numParams + 1) args.size))
      let projection := e.getAppFn.constName?.any (#[``And.left, ``And.right,
        ``Iff.mp, ``Iff.mpr, ``Subtype.property, ``Eq.mp, ``Eq.mpr, ``Eq.symm].contains ·)
      if projection || e.isProj || e.getAppFn.isLambda then
        return .done (← withTransparency .all <| whnf e)
      return .done e)
    let proof ← inlineLookupSupport base proof
    let proof ← withLookupPreparation (some budget) <| pure (detachLookupExpression proof)
    certificateEscaped.set true
    return proof
  return {table with
    memo? := some memo, budget? := some budget,
    close? := some close, finish? := some finish,
    load? := some fun entry head queryType => do
      let context ← readThe Core.Context
      if entry.module.startsWith "D5." && !(← verified.get) then
        let some disk := table.disk? | throwError "lookup.candidate_without_snapshot"
        let check ← withLookupPreparation (some budget) <| IO.Process.output {
          cmd := "git", args := #["diff", "--quiet", disk.header.basis, "--", "D5"]}
        unless check.exitCode == 0 do throwError "lookup.candidate_snapshot_changed"
        verified.set true
      -- cache.get's result is gone before acquire can release the old module.
      let cached ← (fun ready => ready.bind fun (module, options, source) =>
        if module == entry.module && options == context.options then some source else none) <$> cache.get
      let source ← if let some source := cached then pure source else do
        resetCache
        modifyThe Core.State fun state => {state with cache := {}}
        withLookupPreparation (some budget) <| acquire entry.module.toName context.options
      let query ← getEnv
      -- Native imports carry nested inductives, recursors and generated
      -- declarations intact. Only query vocabulary is reconstructed here.
      let native ← withLookupPreparation (some budget) do
        let mut native := source
        -- Preserve query tables without any candidate registrations. This
        -- deterministic copy creates no metavariables or choice points.
        unless source.header.moduleNames.extract 0 query.header.moduleNames.size ==
            query.header.moduleNames do
          throwError "lookup.native_module_index_mismatch"
        for extension in ← persistentEnvExtensionsRef.get do
          let ext := extension.toEnvExtension
          let queryState := ext.getState (asyncMode := .sync) query
          let importedState := ext.getState (asyncMode := .sync) source
          native := ext.setState (asyncMode := .sync) native
            {queryState with importedEntries := importedState.importedEntries}
        return native
      setEnv native
      resetCache
      modifyThe Core.State fun state => {state with cache := {}}
      let transport : TransportContext := {
        source := query, enclosingBudget := true, certifiedBasis := true,
        lookupPreparation? := some budget}
      discard <| withLookupPreparation (some budget) <|
        copyCertificateExpression transport queryType
      for decl in ← getLCtx do
        discard <| withLookupPreparation (some budget) <|
          copyCertificateExpression transport decl.type
        if let some value := decl.value? then
          discard <| withLookupPreparation (some budget) <|
            copyCertificateExpression transport value
      -- Goal metavariables live in Meta state, independently of imports.
      -- Copy their types' computational vocabulary without importing T or S.
      let some info := (source.setExporting false).find? entry.leanName
        | throwError "lookup.module_candidate_missing"
      if info.isUnsafe then return {}
      unless unloadedPossibleView source head info.type do return {}
      let params := info.levelParams.map ownedLookupName
      let levels ← params.mapM fun _ => mkFreshLevelMVar
      let type := info.type.instantiateLevelParams info.levelParams levels
      let placeholder ← mkFreshExprMVar type
      return {values := #[placeholder], certify := do
        lookupPhase s!"candidate/signature-matched name={entry.name} module={entry.module}"
        placeholder.mvarId!.assign (mkConst entry.leanName levels)}}


/-- Explicit inspection of a production reading in its exact query environment.
The production entry leaves this callback absent. -/
abbrev ReadingDiagnostic := LookupTable → Option ImportState → GraphReading → MetaM Unit

private unsafe def runCore (source base : Environment) (request : Request)
    (lookupComplete : Bool) (disk? : Option DiskLookup.Index := none)
    (sharedImports? : Option ImportState := none)
    (implicationModules? : Option (Array Name) := none)
    (diagnostic? : Option ReadingDiagnostic := none) : IO Observation := do
  isolationUnitReadings.set #[]
  isolationUnitCount.set 0
  isolationRejection.set none
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
      match ← prepare source clean request true (originalBaseline? := some base) with
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
        environment := base, complete := lookupComplete, enabled, disk?, implicationModules?} sharedImports?
      let reading ← withEnv graphEnv <| evaluateGraph graph (some table)
        request.certificates request.edgeCertificates
        (positiveEligible := presentation == .exhausted && structureChecked)
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
        rejection? := ← isolationRejection.get,
        presentationComplete := match presentation with | .incomplete _ => false | _ => true}
      let baseRun := intervalRun reading.graph reading.baseline
      if let some diagnostic := diagnostic? then
        withEnv graphEnv <| diagnostic table sharedImports? reading
      let pairedGraph := {reading.graph with edges := reading.graph.edges.map (fun edge => {edge with cost := edge.pairedCost})}
      let pairRun := match structureFailure with
        | some failure => .incomplete failure
        | none => intervalRun pairedGraph reading.paired
      let attempts := baselineProof?.toArray.map fun proof =>
        {strategy := "graph/assembled-zero", outcome := .found, proof? := some proof : Attempt}
      let pairAttempts := pairedProof?.toArray.map fun proof =>
        {strategy := "graph/assembled-zero", outcome := .found, proof? := some proof : Attempt}
      profilePhase "query/assembly-end"
      return {
        target := request.target, base := baseRun, paired := pairRun,
        verdict := classifyGraph reading, attempts, pairAttempts,
        targetChecked := true, structureChecked, structureClean := structureChecked,
        presentation, presentationEvidence?, presentationDetail, graph? := some reading,
        reason := structureReason, isolationUnits := ← isolationUnitReadings.get,
        isolationUnitCount := ← isolationUnitCount.get}
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
    (sharedImports : ImportState := default) (fixture : Bool := false)
    (diagnostic? : Option ReadingDiagnostic := none) : IO Observation := do
  unless source.contains request.target do
    return {
      target := request.target, verdict := .insufficient, base := .incomplete .missing,
      paired := .incomplete .missing, reason := "search.missing_target"}
  try
    enableInitializersExecution
    let mut delivery := #[]
    for n in #[request.target] ++ request.additions do
      if let some index := source.getModuleIdxFor? n then
        delivery := delivery.push source.header.moduleNames[index.toNat]!
    let ancestors ← targetBaselineImports request.baselineCommit delivery source request.target request.baseline
    let modules := ((ancestors.filter (·.toString.startsWith "D5.")) ++ request.baseline).foldl
      (fun out n => if out.contains n then out else out.push n) (#[] : Array Name)
    let imports : Array Import := #[{module := `Mathlib}] ++ modules.map (fun n => {module := n})
    profilePhase "query/base-import-start"
    let (base, baseImports) ← withImporting do
      let (_, state) ← (importModulesCore imports).run sharedImports
      let base ← finalizeImport state imports options 0 (leakEnv := false) (loadExts := true)
      pure (base, state)
    profilePhase "query/base-import-end"
    let catalog ← baselineCatalog request.baselineCommit delivery base
    let disk? ← if fixture then
      try
        pure (some (← DiskLookup.openFixtureIndex
          s!"build/lean-inspector/search-reduction-test-index/{request.baselineCommit}"
          request.baselineCommit mathlibRevision catalog.excluded))
      catch _ => pure none
      else do
        let directory := (← IO.getEnv "SEARCH_REDUCTION_INDEX").getD
          s!"build/lean-inspector/lookup-index/{request.baselineCommit}"
        try
          pure (some (← DiskLookup.openIndex directory
            request.baselineCommit mathlibRevision catalog.excluded))
        catch ex => throw <| IO.userError s!"search.production_index_open_failed:{directory}:{ex}"
    let result ← runCore source base request disk?.isSome disk? (some baseImports) (some ancestors) diagnostic?
    let used := request.additions.filter fun name =>
      result.graph?.any fun reading => reading.selectedSeeds.any fun id =>
        reading.graph.vertices.any fun vertex => vertex.id == id &&
          vertex.structureProof?.any (fun proof => proof.getUsedConstants.contains name)
    return {result with
      catalogCount := catalog.eligible.size, loadedModules := catalog.loaded,
      catalogExcluded := catalog.excluded, scope := "B_T",
      catalogVerified := true, pairedStructureUse := used,
      isolationUnits := ← isolationUnitReadings.get,
      isolationUnitCount := ← isolationUnitCount.get}
  catch ex =>
    unless fixture do throw ex
    return {
      target := request.target, verdict := .insufficient, base := .incomplete .isolation,
      paired := .incomplete .isolation, presentation := .incomplete .isolation,
      reason := s!"search.catalog_incomplete:{ex}"}

end LeanInformationAudit.SearchReduction
