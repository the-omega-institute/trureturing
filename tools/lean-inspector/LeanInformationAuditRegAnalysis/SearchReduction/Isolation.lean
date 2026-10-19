import LeanInformationAuditRegAnalysis.SearchReduction.Presentation

/-! Compiled-environment isolation and immutable baseline provenance. -/

namespace LeanInformationAudit.SearchReduction
open Lean Meta
open LeanInformationAudit.Tests.SearchReduction (classifyCertified Failure)

/-- The source environment is used only to recover types and check compiled
values. Probe environments start from independent baseline imports. -/
structure Request where
  target : Name
  baseline : Array Name
  additions : Array Name := #[]
  baselineCommit : String
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

/-- Only vocabulary definitions can be copied to the baseline. A proof-valued
constant, even private or an instance hidden under data, rejects isolation. -/
partial def copyVocabulary (source : Environment) (n : Name)
    (visiting : NameSet := {}) : MetaM Unit := do
  if (← getEnv).contains n then return
  if visiting.contains n then throwError "search.unsupported_mutual_vocabulary: {n}"
  let info ← checkedSource source n
  if ← withEnv source (isProp info.type) then
    throwError "search.hidden_proof_dependency: {n}"
  let .defnInfo value := info
    | throwError "search.unsupported_vocabulary_kind: {n}"
  unless value.safety == .safe do throwError "search.unsafe_vocabulary: {n}"
  discard <| withEnv source <| Meta.transform value.value (pre := fun e => do
    if ← isProof e then throwError "search.proof_embedded_in_vocabulary: {n}"
    return .continue)
  for dep in info.getUsedConstantsAsSet do
    copyVocabulary source dep (visiting.insert n)
  addDecl (.defnDecl value)
  setReducibilityStatus n .reducible

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
  for dep in info.type.getUsedConstants do copyVocabulary source dep
  if (← singleSourceConversion targetType info.type).isSome ||
      (← certifiedRestatement targetType info.type index) then
    throwError "search.target_restatement: {n}"
  if (← getEnv).contains n then return
  for dep in info.getUsedConstantsAsSet do
    if (← getEnv).contains dep then continue
    let depInfo ← sourceInfo source dep
    if ← withEnv source (isProp depInfo.type) then
      copyStructure source target targetType dep index (visiting.insert n)
    else
      copyVocabulary source dep
  match info with
  | .thmInfo value => addDecl (.thmDecl value)
  | .defnInfo value => addDecl (.defnDecl value)
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
  let mut result := #[info.type]
  for dep in info.getUsedConstantsAsSet do
    if (← getEnv).contains dep then continue
    let depInfo ← sourceInfo source dep
    if ← withEnv source (isProp depInfo.type) then
      result := result ++ (← structureTypes source dep (seen.insert n))
  return result

private def prepare (source base : Environment) (request : Request)
    (paired : Bool) : IO (Except (Failure × String) (Environment × ConstantInfo)) := do
  let work : CoreM (Environment × ConstantInfo) := MetaM.run' do
    let target ← checkedSource source request.target
    unless ← withEnv source (isProp target.type) do
      throwError "search.target_not_proposition: {request.target}"
    for dep in target.type.getUsedConstants do copyVocabulary source dep
    if paired then
      let index ← factIndex
      let mut types := #[]
      for n in request.additions do
        if base.contains n then throwError "search.structure_already_in_baseline: {n}"
        let info ← checkedSource source n
        for dep in info.type.getUsedConstants do copyVocabulary source dep
        let (present, _, _) ← baselinePresentation (← getEnv) info.levelParams info.type #[] (some index)
        if present == .found then throwError "search.structure_baseline_presentation: {n}"
        if let .incomplete _ := present then throwError "search.structure_presentation_incomplete: {n}"
        types := types ++ (← structureTypes source n)
      for type in types do
        for dep in type.getUsedConstants do copyVocabulary source dep
      if ← collectionLeak target.type types then throwError "search.structure_collection_restatement"
      for n in request.additions do
        copyStructure source request.target target.type n index
    return (← getEnv, target)
  try
    let context : Core.Context := {
      fileName := "<R_v1 isolation>", fileMap := default, options := options,
      initHeartbeats := ← IO.getNumHeartbeats }
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

unsafe def run (source : Environment) (request : Request) : IO Observation := do
  let unknown (reason : String) (failure := LeanInformationAudit.Tests.SearchReduction.Failure.isolation) : Observation := {
    target := request.target, base := .incomplete failure,
    paired := .incomplete failure, verdict := .insufficient, reason }
  try
    unless source.contains request.target do
      return unknown "search.missing_target" .missing
    -- Attributes, instances, macros, simp sets and theorem indexes all come
    -- from B. No extension state from source is merged into these imports.
    enableInitializersExecution
    let mathlib ← importModules #[{module := `Mathlib}] options 0
      (leakEnv := true) (loadExts := true)
    let hints ← strategies mathlib
    enableInitializersExecution
    let base ← importModules (#[{module := `Mathlib}] ++
      request.baseline.map (fun n => {module := n})) options 0
      (leakEnv := true) (loadExts := true)
    if let .error reason ← checkBaseline request base then return unknown reason
    if hints.isEmpty then return unknown "search.missing_registered_strategies"
    let prepared ← prepare source base request false
    let .ok (clean, target) := prepared
      | let (failure, reason) := match prepared with
          | .error failure => failure | _ => (.isolation, "search.isolation_failed")
        return unknown reason failure
    if clean.contains request.target then return unknown "search.target_already_in_baseline"
    let (baseRun, attempts, index?) ← searchIndexed clean target.levelParams target.type #[] hints
    let moduleNames := clean.header.moduleNames
    let preferred := (clean.constants.toList.toArray.qsort
      (fun a b => Name.quickLt a.1 b.1)).filterMap fun (name, _) =>
      match clean.getModuleIdxFor? name with
      | some idx => if request.baseline.contains moduleNames[idx.toNat]! then some name else none
      | none => none
    let proofDependencies := (attempts.filterMap (·.proof?)).foldl
      (fun names proof => names ++ proof.getUsedConstants) #[]
    let preferred := proofDependencies ++ preferred
    let (presentation, presentationEvidence?, presentationDetail) ←
      baselinePresentation clean target.levelParams target.type preferred index? (baseRun != .found)
    let observed : Observation := {
      target := request.target, base := baseRun, paired := .incomplete .undecided,
      verdict := classifyCertified true presentation baseRun false false (.incomplete .undecided),
      attempts, targetChecked := true, presentation, presentationEvidence?, presentationDetail }
    if observed.verdict == .bindOnly then return observed
    if let .incomplete _ := presentation then
      return {observed with reason := "search.presentation_incomplete"}
    if request.additions.isEmpty then
      return {
        target := request.target, base := baseRun, paired := .incomplete .missing,
        verdict := .insufficient, attempts, targetChecked := true,
        presentation, presentationEvidence?, presentationDetail, reason := "search.empty_structure" }
    for n in request.additions do
      unless source.contains n do
        return { (unknown s!"search.missing_structure: {n}" .missing) with
          base := baseRun, attempts, targetChecked := true,
          presentation, presentationEvidence?, presentationDetail }
    let preparedS ← prepare source base request true
    let .ok (pairedEnv, _) := preparedS
      | let (failure, reason) := match preparedS with
          | .error failure => failure | _ => (.isolation, "search.structure_isolation_failed")
        return { (unknown reason failure) with
          base := baseRun, attempts, targetChecked := true,
          presentation, presentationEvidence?, presentationDetail }
    let (pairRun, pairAttempts) ← search pairedEnv target.levelParams target.type request.additions hints
    return {
      target := request.target, base := baseRun, paired := pairRun,
      verdict := classifyCertified true presentation baseRun true true pairRun, attempts, pairAttempts,
      targetChecked := true, structureChecked := true, structureClean := true,
      presentation, presentationEvidence?, presentationDetail,
      reason := if pairRun == .exhausted then "search.structure_insufficient_to_close" else ""}
  catch ex => return unknown s!"search.execution: {ex}" .execution

end LeanInformationAudit.SearchReduction
