import LeanInformationAuditRegAnalysis.SearchReduction.Presentation
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CasesOn
import Lean.Meta.Constructions.RecOn
import Lean.Meta.Constructions.NoConfusion
import Lean.Meta.Constructions.BRecOn
import Lean.Meta.Structure
import LeanInformationAuditRegAnalysis.SearchReduction.PinnedDeriving

/-! Prefix reconstruction. Author certificate bodies never enter the search environment. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

abbrev transportVersion : String := "prefix-reconstruction-independent-units-v1"
abbrev reconstructionBudget : Nat := 200000

private initialize referenceEnvironmentCache : IO.Ref (Option Environment) ← IO.mkRef none
private initialize referenceHintCache :
    IO.Ref (Option (Array (Nat × TSyntax `tactic))) ← IO.mkRef none

/-- An immutable pinned Mathlib import can be shared without merging any
candidate extension state or repeating its resident module graph. -/
def referenceEnvironment : IO Environment := do
  if let some env := ← referenceEnvironmentCache.get then return env
  let env ← importModules #[{module := `Mathlib}] options 0
    (leakEnv := true) (loadExts := true)
  referenceEnvironmentCache.set (some env)
  return env

/-- The immutable strategy list always comes from the pinned Mathlib import,
including when a clean vocabulary prefix is already available. -/
def referenceHints : IO (Array (Nat × TSyntax `tactic)) := do
  if let some hints := ← referenceHintCache.get then return hints
  let hints ← strategies (← referenceEnvironment)
  referenceHintCache.set (some hints)
  return hints

structure VocabularyCertificate where
  owner : Name
  type : Expr
  proof : Expr
  axioms : Array Name

structure TransportContext where
  source : Environment
  target : Name := .anonymous
  targetType : Expr := mkSort .zero
  forbidden : NameSet := {}
  visiting : NameSet := {}
  bound : NameSet := {}
  certificates? : Option (IO.Ref (Array VocabularyCertificate)) := none
  budgetStart : Nat := 0
  searchHeartbeats? : Option (IO.Ref Nat) := none
  budgetExcludedStart : Nat := 0
  regenerated? : Option (IO.Ref NameSet) := none

private def sourceConstant (ctx : TransportContext) (n : Name) : MetaM ConstantInfo := do
  let some info := (ctx.source.setExporting false).find? n
    | throwError "search.missing_vocabulary: {n}"
  if info.isUnsafe then throwError "search.unsafe_vocabulary: {n}"
  return info

private def localParameters : MetaM (Array Expr) := do
  let mut xs := #[]
  for decl in ← getLCtx do xs := xs.push decl.toExpr
  return xs

/-- A source projection is recognized by its expression shape, then regenerated
from the rebuilt constructor telescope. No source proof value is installed. -/
def projectionShape (info : ConstantInfo) : Option (Name × Nat) := do
  let mut body ← info.value? (allowOpaque := true)
  while body.isLambda do body := body.bindingBody!
  let .proj owner index _ := body | none
  return (owner, index)

/-- Inline source-owned helpers to expose the actual author edge. Only its
head and the data-slot shape cross into R_loc; no source theorem is installed. -/
private partial def vocabularySpine (source clean : Environment) (proof : Expr)
    (seen : NameSet := {}) : MetaM (Option Expr × Array (Option Expr)) := do
  let proof := proof.consumeMData.headBeta
  if let .lam name domain body kind := proof then
    return ← withLocalDecl name kind domain fun x =>
      vocabularySpine source clean (body.instantiate1 x) seen
  let head := proof.getAppFn
  if let .const name levels := head then
    if !clean.contains name then
      if seen.contains name then return (none, #[])
      if let some info := (source.setExporting false).find? name then
        if let some value := info.value? (allowOpaque := true) then
          return ← vocabularySpine source clean
            (mkAppN (value.instantiateLevelParams info.levelParams levels) proof.getAppArgs)
            (seen.insert name)
      return (none, #[])
  else if !head.isFVar then return (none, #[])
  let scope ← localParameters
  let data ← proof.getAppArgs.mapM fun arg => do
    if ← isProof arg then return none
    return some (← mkLambdaFVars scope arg)
  return (some (← mkLambdaFVars scope head), data)

private def checkReconstructionBudget (ctx : TransportContext) : MetaM Unit := do
  if let some used := ctx.searchHeartbeats? then
    let work := (← IO.getNumHeartbeats) - ctx.budgetStart - ((← used.get) - ctx.budgetExcludedStart)
    if work > reconstructionBudget * 1000 then
      throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
        m!"search.vocabulary_work_budget: {work / 1000}/{reconstructionBudget}"

/-- Install only kernel-checked declarations from a clean pinned generator;
none of its environment extensions or registrations are transferred. -/
private partial def installGenerated (generated : Environment) (n : Name) : MetaM Unit := do
  if (← getEnv).contains n then return
  let some info := (generated.setExporting false).find? n
    | throwError "search.generated_dependency_missing: {n}"
  for dep in info.getUsedConstantsAsSet do installGenerated generated dep
  match info with
  | .defnInfo value => addDecl (.defnDecl value)
  | .thmInfo value => discard <| checkProof n value.levelParams value.type value.value
  | _ => throwError "search.generated_dependency_unsupported: {n}"

/-- A preflight counts the complete computational closure, stopping at maximal
proof bodies and inspecting only their closed obligation types. It never runs R. -/
private structure Inventory where
  source : Environment
  base : Environment
  seen : IO.Ref NameSet
  obligations : IO.Ref Nat
  leafBound : IO.Ref Nat

/-- Structural splitting can only discard leaves from this type-only tree. -/
private partial def potentialLeaves (type : Expr) : MetaM Nat := do
  let type ← withReducible <| whnf type
  if type.isForall then
    return ← forallTelescopeReducing type fun _ body => potentialLeaves body
  if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then
    return (← potentialLeaves type.appFn!.appArg!) + (← potentialLeaves type.appArg!)
  return 1

mutual
  private partial def inventoryConstant (plan : Inventory) (n : Name) : MetaM Unit := do
    if plan.base.contains n || (← plan.seen.get).contains n then return
    plan.seen.modify (·.insert n)
    let some info := (plan.source.setExporting false).find? n
      | throwError "search.missing_vocabulary: {n}"
    withLCtx {} {} do
      match info with
      | .inductInfo value =>
        for owner in value.all do
          plan.seen.modify (·.insert owner)
          let some (.inductInfo member) := (plan.source.setExporting false).find? owner
            | throwError "search.inventory_group_missing: {owner}"
          inventoryExpression plan member.type
          for ctor in member.ctors do
            plan.seen.modify (·.insert ctor)
            inventoryExpression plan ((plan.source.setExporting false).find? ctor).get!.type
      | .ctorInfo value => inventoryConstant plan value.induct
      | .recInfo value => for owner in value.all do inventoryConstant plan owner
      | _ =>
        inventoryExpression plan info.type
        -- The overcount also includes auxiliaries that a pinned generator
        -- replaces; generated execution itself remains one declaration unit.
        if let some body := info.value? (allowOpaque := true) then
          inventoryExpression plan body

  private partial def inventoryExpression (plan : Inventory) (e : Expr) : MetaM Unit := do
    discard <| Meta.transform e (pre := fun part => do
      if ← isProof part then
        plan.obligations.modify (· + 1)
        let xs ← localParameters
        let closed ← mkForallFVars xs (← inferType part)
        let leaves ← potentialLeaves closed
        plan.leafBound.modify (· + leaves)
        inventoryExpression plan closed
        return .done part
      if let .const n _ := part then inventoryConstant plan n
      if let .proj n _ _ := part then inventoryConstant plan n
      return .continue)
end

def vocabularyBudgetPreflight (source : Environment) (roots : Array Name) : MetaM Unit := do
  let started ← IO.getNumHeartbeats
  try
    withTheReader Core.Context (fun reader => {reader with
        initHeartbeats := started, maxHeartbeats := reconstructionBudget * 1000}) do
      let plan : Inventory := {
        source, base := (← getEnv), seen := (← IO.mkRef {}),
        obligations := (← IO.mkRef 0), leafBound := (← IO.mkRef 0)}
      withEnv source do
        for root in roots do inventoryConstant plan root
      -- Includes constructor/recursor forwarding units as well as complete groups.
      let groups := (← plan.seen.get).size
      let obligations ← plan.obligations.get
      let units := 1 + groups + obligations
      let searchUnits := 2 * obligations + (← plan.leafBound.get) * 3
      IO.eprintln s!"vocabulary prior budget: semantics=independent_units, roots={roots}, declaration_units={groups}, obligation_units={obligations}, unit_limit={reconstructionBudget * 1000}, prior_work_heartbeats_bound={units * reconstructionBudget * 1000}, preflight_internal_heartbeats={(← IO.getNumHeartbeats) - started}; prior_R_command_units_bound={searchUnits}, prior_total_heartbeats_bound={(units + searchUnits) * reconstructionBudget * 1000}"
      checkSystem "vocabulary preflight"
  catch ex =>
    if ex.isMaxHeartbeat then
      throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
        m!"search.vocabulary_preflight_budget: {roots}: {ex.toMessageData}"
    throw ex

mutual
  partial def transportVocabulary (ctx : TransportContext) (n : Name) : MetaM Unit := do
    if ctx.bound.contains n || (← getEnv).contains n then return
    if ctx.searchHeartbeats?.isNone then vocabularyBudgetPreflight ctx.source #[n]
    let spent ← match ctx.searchHeartbeats? with
      | some spent => pure spent
      | none => IO.mkRef 0
    let ctx := {ctx with
      budgetStart := (← IO.getNumHeartbeats),
      searchHeartbeats? := some spent, budgetExcludedStart := (← spent.get)}
    try
      -- R's independent commands retain their own limits. Their allocation is
      -- excluded from the separate bound on reconstruction work.
      withTheReader Core.Context (fun reader => {reader with maxHeartbeats := 0}) do
        checkReconstructionBudget ctx
        -- A referenced global definition owns its telescope. Parameters of the
        -- expression that mentioned it must never enter its proof obligations.
        withLCtx {} {} <| transportVocabularyCore ctx n
        checkReconstructionBudget ctx
        let total := (← IO.getNumHeartbeats) - ctx.budgetStart
        let own := total - ((← spent.get) - ctx.budgetExcludedStart)
        spent.modify (· + own)
        IO.eprintln s!"vocabulary unit: owner={n}, own_internal_heartbeats={own}, limit={reconstructionBudget * 1000}"
    catch ex =>
      let own := (← IO.getNumHeartbeats) - ctx.budgetStart -
        ((← spent.get) - ctx.budgetExcludedStart)
      IO.eprintln s!"vocabulary unit failed: owner={n}, own_internal_heartbeats={own}, limit={reconstructionBudget * 1000}"
      if ex.isMaxHeartbeat then
        throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
          m!"search.vocabulary_reconstruction_budget: {n}: {ex.toMessageData}"
      throw ex

  partial def transportVocabularyCore (ctx : TransportContext) (n : Name) : MetaM Unit := do
    if ctx.forbidden.contains n || n == ctx.target then
      throwError "search.target_in_vocabulary_certificate: {n}"
    if ctx.bound.contains n || (← getEnv).contains n then return
    if ctx.visiting.contains n then throwError "search.vocabulary_cycle: {n}"
    let info ← sourceConstant ctx n
    let next := {ctx with visiting := ctx.visiting.insert n}
    match info with
    | .inductInfo value => rebuildInductive next value
    | .ctorInfo value => transportVocabulary ctx value.induct
    | .recInfo value =>
      for owner in value.all do transportVocabulary ctx owner
      unless (← getEnv).contains n do throwError "search.generated_reconstruction_failed: {n}"
    | _ =>
      -- Generated eliminators are generated from the kernel-rebuilt group.
      if let .str owner suffix := n then
        if ["casesOn", "recOn", "noConfusion", "noConfusionType", "below", "brecOn"].contains suffix then
          if let some (.inductInfo _) := (ctx.source.setExporting false).find? owner then
            transportVocabulary ctx owner
            unless (← getEnv).contains n do throwError "search.generated_reconstruction_failed: {n}"
            return
      if let some (owner, index) := projectionShape info then
        transportVocabulary ctx owner
        let ind ← getConstInfoInduct owner
        let ctor ← getConstInfoCtor ind.ctors.head!
        let names := (Array.range (index + 1)).map fun i =>
          {ref := Syntax.missing, projName := if i == index then n else n ++ Name.num `_prefixProjection i : StructProjDecl}
        -- Generate earlier field projections under fresh names solely to obtain
        -- dependent field types. They contain only Expr.proj, never author terms.
        mkProjections owner names false
        unless ← isDefEq (← getConstInfo n).type info.type do
          throwError "search.generated_projection_type_mismatch: {n}"
        return
      if ← regenerateDerived next info then return
      if ← withEnv ctx.source (isProp info.type) then
        throwError "search.certificate_constant_requires_obligation: {n}"
      let .defnInfo value := info
        | throwError "search.generated_reconstruction_failed: {n}"
      let type ← reconstructExpression next n value.type
      let body ← reconstructExpression next n value.value
      addDecl (.defnDecl {value with type, value := body})
      setReducibilityStatus n .reducible
      IO.eprintln s!"vocabulary rebuilt: {n}"

  partial def reconstructExpression (ctx : TransportContext) (owner : Name) (e : Expr) : MetaM Expr :=
    Meta.transform e (pre := fun part => do
      checkReconstructionBudget ctx
      if ← withEnv ctx.source (isProof part) then
        let some spent := ctx.searchHeartbeats? | throwError "search.missing_unit_counter"
        let proofCtx := {ctx with
          budgetStart := (← IO.getNumHeartbeats), budgetExcludedStart := (← spent.get)}
        let type ← withEnv ctx.source (inferType part)
        let xs ← localParameters
        let closed ← mkForallFVars xs type
        -- Reconstruct only the obligation type; the author's term is never
        -- passed to R. The current group and the complete T/S set stay absent.
        let closed ← reconstructExpression proofCtx owner closed
        let levels := (collectLevelParams {} closed).params.toList
        if closed.getUsedConstants.any ctx.bound.contains then
          throwError "search.vocabulary_obligation_unclosed: {owner}: group-local type {closed}"
        let started ← IO.getNumHeartbeats
        -- Only the author's application head is supplied. Its arguments are
        -- abstracted by the same hidden-data reconstructor as graph edges.
        let clean ← getEnv
        let (head?, data) ← withEnv ctx.source <| vocabularySpine ctx.source clean part
        let mut rebuilt ← localRebuild closed head? data [] []
        if rebuilt.cost == .one then
          -- The obligation can need direct proof premises of its author edge.
          -- Price those premises through the same hidden-data graph backend;
          -- only a zero path assembled from clean leaves is admitted.
          rebuilt ← withTheReader Core.Context (fun reader => {reader with
              initHeartbeats := started, maxHeartbeats := localBudget * 1000}) do
            let mut rebuilt := rebuilt
            let sourceProof ← withEnv ctx.source <| mkLambdaFVars xs part
            let raw ← withEnv ctx.source <| extractGraph clean closed sourceProof
            if raw.complete then
              let reading ← evaluateGraph raw
              if let some proof ← assembleZero reading.graph then
                rebuilt := {cost := .zero, proof? := some proof, detail := "kernel-checked-author-graph"}
              else
                rebuilt := {rebuilt with detail := s!"{rebuilt.detail};author-graph:{reprStr reading.baseline}"}
            checkSystem "vocabulary author graph"
            return rebuilt
        let outcome := match rebuilt.cost with
          | .zero => Run.found | .one => .exhausted | .unknown => .incomplete .undecided
        let used := (← IO.getNumHeartbeats) - started
        if let some spent := ctx.searchHeartbeats? then spent.modify (· + used)
        checkReconstructionBudget proofCtx
        IO.eprintln s!"vocabulary obligation: owner={owner}, type={closed}, outcome={reprStr outcome}, detail={rebuilt.detail}, internal_heartbeats={used}"
        let some proof := rebuilt.proof?
          | if outcome == .incomplete .heartbeat then
              throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
                m!"search.vocabulary_obligation_budget: {owner}: {closed}"
            let isTarget ← try
              withEnv ctx.source do
                let defeq := match Kernel.isDefEq ctx.source {} ctx.targetType closed with
                  | .ok equal => equal
                  | .error _ => false
                return defeq || (← singleSourceConversion ctx.targetType closed).isSome ||
                  (← certifiedRestatement ctx.targetType closed)
              catch ex =>
                if ex.isRuntime || ex.isInterrupt then throw ex
                pure false
            if isTarget then throwError "search.target_in_vocabulary_certificate: {owner}: {closed}"
            throwError "search.vocabulary_obligation_unclosed: {owner}: {closed}: {reprStr outcome}"
        let beforeCheck ← getEnv
        let checked ← checkProof (← mkFreshUserName `_prefixCertificate) levels closed proof
        setEnv beforeCheck
        if let some certificates := ctx.certificates? then
          certificates.modify (·.push {owner, type := closed, proof, axioms := checked})
        unless standardAxioms checked do throwError "search.vocabulary_certificate_axioms: {owner}"
        IO.eprintln s!"vocabulary certificate checked: owner={owner}, strategy={rebuilt.detail}, axioms={checked}"
        checkReconstructionBudget proofCtx
        let own := (← IO.getNumHeartbeats) - proofCtx.budgetStart -
          ((← spent.get) - proofCtx.budgetExcludedStart)
        spent.modify (· + own)
        IO.eprintln s!"vocabulary obligation unit: owner={owner}, own_internal_heartbeats={own}, limit={reconstructionBudget * 1000}"
        -- Inline the result. No certificate constant becomes a searchable fact.
        let args ← xs.filterM fun x => return !(← getFVarLocalDecl x).isLet
        return .done (mkAppN proof args)
      if let .const n _ := part then transportVocabulary ctx n
      if let .proj n _ _ := part then transportVocabulary ctx n
      return .continue)

  /-- Only pinned built-in handlers run. The source value is used solely for
  kernel equality against the regenerated computational skeleton, never installed. -/
  partial def regenerateDerived (ctx : TransportContext) (info : ConstantInfo) : MetaM Bool := do
    let shape ← withEnv ctx.source <| forallTelescope info.type fun _ body => do
      let cls := body.getAppFn.constName?.getD .anonymous
      let some owner := body.getAppArgs.findSome? (fun arg =>
        let name := arg.getAppFn.constName?.getD .anonymous
        match (ctx.source.setExporting false).find? name with
        | some (.inductInfo _) => some name
        | _ => none)
        | return none
      unless pinnedDerivingClasses.contains cls do
        if (← isClass? body).isSome then
          throwError "search.derived_generator_unsupported: {info.name}: class {cls}"
        return none
      return some (cls, owner)
    let some (cls, owner) := shape | return false
    transportVocabulary ctx owner
    let before ← getEnv
    let handler := pinnedDeriving cls #[owner]
    let cctx : Elab.Command.Context := {fileName := "<pinned deriving>", fileMap := default, cancelTk? := none, snap? := none}
    let state : Elab.Command.State := {
      env := before, maxRecDepth := 1000, scopes := [{header := "", currNamespace := owner.getPrefix, opts := options}]}
    let result ← (handler.run cctx |>.run state).toIO'
    let generated ← match result with
      | .ok (true, state) =>
        if state.messages.hasErrors then throwError "search.derived_generator_failed: {info.name}"
        pure state.env
      | .ok _ => throwError "search.derived_generator_unsupported: {info.name}"
      | .error ex =>
        if ex.isMaxHeartbeat || ex.isInterrupt then throw ex
        throwError "search.derived_generator_failed: {info.name}: {ex.toMessageData}"
    let added := generated.constants.foldStage2 (fun acc name ci =>
      if before.contains name then acc else acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
    let mut found := none
    for (_, candidate) in added do
      let type := candidate.type.instantiateLevelParams candidate.levelParams (info.levelParams.map Level.param)
      let equal := match Kernel.isDefEq generated {} type info.type with
        | .ok equal => equal
        | .error _ => false
      if equal then found := some candidate
    let some candidate := found
      | throwError "search.derived_generator_type_missing: {info.name}"
    let some body := candidate.value? (allowOpaque := true)
      | throwError "search.derived_generator_value_missing: {info.name}"
    let body := body.instantiateLevelParams candidate.levelParams (info.levelParams.map Level.param)
    -- Check in the union only for comparison; source extensions never enter B.
    let comparison ← withEnv ctx.source do
      for (name, _) in added do installGenerated generated name
      getEnv
    let equal := match Kernel.isDefEq comparison {} body (info.value?.getD (.sort .zero)) with
      | .ok equal => equal
      | .error _ => false
    unless equal do throwError "search.derived_computation_mismatch: {info.name}"
    -- Discard handler attributes/instance registration. Retain kernel declarations only.
    for (name, _) in added do
      let xs ← withEnv generated (collectAxioms name)
      unless standardAxioms xs do throwError "search.derived_generator_axioms: {name}"
    for (name, _) in added do
      installGenerated generated name
      if let some names := ctx.regenerated? then names.modify (·.insert name)
    unless (← getEnv).contains info.name do
      match info with
      | .defnInfo original => addDecl (.defnDecl {original with value := body})
      | .thmInfo original => discard <| checkProof info.name original.levelParams original.type body
      | _ => throwError "search.derived_generator_name_mismatch: {info.name}"
      if let some names := ctx.regenerated? then names.modify (·.insert info.name)
    IO.eprintln s!"vocabulary derived regenerated: owner={owner}, class={cls}, instance={info.name}, axioms=std3"
    return true

  partial def rebuildInductive (ctx : TransportContext) (value : InductiveVal) : MetaM Unit := do
    if value.numNested != 0 then
      throwError "search.generated_reconstruction_failed: nested group {value.all}"
    let group := value.all
    let signatureContext := {ctx with bound := group.foldl (fun s n => s.insert n) ctx.bound}
    let mut types := []
    for n in group do
      let .inductInfo member ← sourceConstant ctx n
        | throwError "search.generated_reconstruction_failed: group {n}"
      let mut ctors := []
      for c in member.ctors do
        let ctor ← sourceConstant ctx c
        let type ← reconstructExpression signatureContext c ctor.type
        ctors := ctors ++ [{name := c, type : Constructor}]
      let type ← reconstructExpression signatureContext n member.type
      types := types ++ [{name := n, type, ctors : InductiveType}]
    addDecl (.inductDecl value.levelParams value.numParams types false)
    Lean.compileDecls group.toArray
    for n in group do
      mkCasesOn n
      mkRecOn n
      mkCtorIdx n
      mkNoConfusion n
      mkBelow n
    for n in group do mkBRecOn n
    IO.eprintln s!"vocabulary inductive group rebuilt: {group}"
end

/-- The import and witness-export paths use the same reconstruction kernel. -/
def copyVocabulary (source : Environment) (n : Name) (visiting : NameSet := {}) : MetaM Unit :=
  transportVocabulary {source, visiting} n

end LeanInformationAudit.SearchReduction
