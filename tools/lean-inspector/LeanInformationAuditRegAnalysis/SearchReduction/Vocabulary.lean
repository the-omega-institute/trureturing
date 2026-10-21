import LeanInformationAuditRegAnalysis.SearchReduction.Presentation
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CasesOn
import Lean.Meta.Constructions.RecOn
import Lean.Meta.Constructions.NoConfusion
import Lean.Meta.Constructions.BRecOn
import Lean.Meta.Structure
import LeanInformationAuditRegAnalysis.SearchReduction.PinnedDeriving

/-! Prefix reconstruction with kernel-checked inline certificate payloads. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

abbrev transportVersion : String := "prefix-reconstruction-checked-certificate-copy-v3"
abbrev reconstructionBudget : Nat := 200000

private initialize referenceEnvironmentCache : IO.Ref (Option Environment) ← IO.mkRef none

/-- An immutable pinned Mathlib import can be shared without merging any
candidate extension state or repeating its resident module graph. -/
def referenceEnvironment : IO Environment := do
  if let some env := ← referenceEnvironmentCache.get then return env
  let env ← importModules #[{module := `Mathlib}] options 0
    (leakEnv := true) (loadExts := true)
  referenceEnvironmentCache.set (some env)
  return env

structure TransportContext where
  source : Environment
  target : Name := .anonymous
  targetType : Expr := mkSort .zero
  forbidden : NameSet := {}
  visiting : NameSet := {}
  bound : NameSet := {}
  budgetStart : Nat := 0
  /-- Query copies keep the enclosing frozen allocation, without declaration units. -/
  enclosingBudget : Bool := false
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

private def checkReconstructionBudget (ctx : TransportContext) : MetaM Unit := do
  if ctx.enclosingBudget then checkSystem "lookup.vocabulary_copy"
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
        obligations := (← IO.mkRef 0)}
      withEnv source do
        for root in roots do inventoryConstant plan root
      -- Includes constructor/recursor forwarding units as well as complete groups.
      let groups := (← plan.seen.get).size
      let obligations ← plan.obligations.get
      let units := 1 + groups + obligations
      IO.eprintln s!"vocabulary prior budget: semantics=checked_inline_copy, roots={roots}, declaration_units={groups}, certificate_units={obligations}, unit_limit={reconstructionBudget * 1000}, prior_work_heartbeats_bound={units * reconstructionBudget * 1000}, preflight_internal_heartbeats={(← IO.getNumHeartbeats) - started}, R_command_units=0"
      checkSystem "vocabulary preflight"
  catch ex =>
    if ex.isMaxHeartbeat then
      throw <| Exception.error (← getRef) <| .tagged `runtime.maxHeartbeats
        m!"search.vocabulary_preflight_budget: {roots}: {ex.toMessageData}"
    throw ex

mutual
  partial def transportVocabulary (ctx : TransportContext) (n : Name) : MetaM Unit := do
    if ctx.bound.contains n || (← getEnv).contains n then return
    if ctx.enclosingBudget then
      checkReconstructionBudget ctx
      withLCtx {} {} <| transportVocabularyCore ctx n
      checkReconstructionBudget ctx
      return
    if ctx.searchHeartbeats?.isNone then vocabularyBudgetPreflight ctx.source #[n]
    let spent ← match ctx.searchHeartbeats? with
      | some spent => pure spent
      | none => IO.mkRef 0
    let ctx := {ctx with
      budgetStart := (← IO.getNumHeartbeats),
      searchHeartbeats? := some spent, budgetExcludedStart := (← spent.get)}
    try
      -- Completed nested declaration work has its own bound and is excluded
      -- from the current reconstruction unit's heartbeat allocation.
      withTheReader Core.Context (fun reader => {reader with maxHeartbeats := 0}) do
        checkReconstructionBudget ctx
        -- A referenced global definition owns its telescope. Parameters of the
        -- expression that mentioned it must never enter its certificate telescope.
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

  /-- Copy a side proof without adding its source theorem to the prefix. Its
  computational dependencies use the same reconstructed vocabulary. -/
  partial def copyCertificateExpression (ctx : TransportContext) (e : Expr) : MetaM Expr :=
    Meta.transform e (pre := fun part => do
      checkReconstructionBudget ctx
      if let .const n levels := part then
        if ctx.bound.contains n || (← getEnv).contains n then return .continue
        if n == ctx.target then
          throwError "search.target_in_vocabulary_certificate: {n}"
        if ctx.visiting.contains n then throwError "search.vocabulary_cycle: {n}"
        let info ← sourceConstant ctx n
        if ← withEnv ctx.source (isProp info.type) then
          let some body := info.value? (allowOpaque := true)
            | throwError "search.vocabulary_certificate_value_missing: {n}"
          let copied ← copyCertificateExpression
            {ctx with visiting := ctx.visiting.insert n}
            (body.instantiateLevelParams info.levelParams levels)
          return .done copied
        transportVocabulary ctx n
      if let .proj n _ _ := part then transportVocabulary ctx n
      return .continue)

  partial def reconstructExpression (ctx : TransportContext) (owner : Name) (e : Expr) : MetaM Expr :=
    Meta.transform e (pre := fun part => do
      checkReconstructionBudget ctx
      -- Existing kernel vocabulary requires no transport or proof expansion.
      let env ← getEnv
      if part.getUsedConstants.all env.contains then return .done part
      if ← withEnv ctx.source (isProof part) then
        let type ← withEnv ctx.source (inferType part)
        -- Transform caches repeated payload expressions across binder scopes.
        -- Only their actual free variables may occur in a cached replacement.
        let used ← (Lean.collectFVars (Lean.collectFVars {} part) type).addDependencies
        let xs := (← localParameters).filter (fun x => used.fvarSet.contains x.fvarId!)
        let closed ← mkForallFVars xs type (generalizeNondepLet := false)
        let closed ← reconstructExpression ctx owner closed
        if closed.getUsedConstants.any ctx.bound.contains then
          throwError "search.vocabulary_certificate_unclosed: {owner}: group-local type {closed}"
        let proof ← copyCertificateExpression ctx
          (← mkLambdaFVars xs part (generalizeNondepLet := false))
        let levels := (collectLevelParams (collectLevelParams {} closed) proof).params.toList
        let beforeCheck ← getEnv
        let checked ← checkProof (← mkFreshUserName `_prefixCertificate) levels closed proof
        setEnv beforeCheck
        unless standardAxioms checked do
          throwError "search.vocabulary_certificate_axioms: {owner}"
        IO.eprintln s!"vocabulary certificate checked: owner={owner}, strategy=inline-author-copy, axioms={checked}"
        -- This proof is payload, never a free premise for a local probe.
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

/-- Inspect T's statement, never its proof. A proof field of a batch-local
vocabulary value must not become a certificate for T merely by transport. -/
def checkTargetVocabularyProjections (source base : Environment) (target : Expr) : MetaM Unit := do
  discard <| Meta.transform target (pre := fun part => do
    let .const owner _ := part.getAppFn | return .continue
    if base.contains owner then return .continue
    let some (.defnInfo _) := (source.setExporting false).find? owner
      | return .continue
    let type ← withEnv source <| inferType part
    if ← withEnv source (isProp type) then return .continue
    let type ← withEnv source <| withReducible <| whnf type
    let .const structureName _ := type.getAppFn | return .continue
    let some (.inductInfo structureInfo) := (source.setExporting false).find? structureName
      | return .continue
    let [constructor] := structureInfo.ctors | return .continue
    let some (.ctorInfo constructorInfo) := (source.setExporting false).find? constructor
      | return .continue
    for index in [:constructorInfo.numFields] do
      let field := Expr.proj structureName index part
      let fieldType ← withEnv source <| inferType field
      unless ← withEnv source (isProp fieldType) do continue
      let closed ← mkForallFVars (← localParameters) fieldType
      let saved ← saveState
      let direct ← withReducible <| isDefEq target closed
      let conversion ← singleSourceConversion target closed
      let converted := direct || conversion.isSome
      saved.restore
      if converted then
        throwError "search.target_in_vocabulary_certificate: {owner}: field {structureName}.{index}: {closed}"
    return .continue)

/-- Reconstruct the complete statement so proof constants in dependent indices
are copied as checked inline payload, never installed as standalone facts. -/
def transportStatement (ctx : TransportContext) (owner : Name) (type : Expr) : MetaM Expr := do
  let spent ← match ctx.searchHeartbeats? with
    | some spent => pure spent
    | none => IO.mkRef 0
  let ctx := {ctx with
    searchHeartbeats? := some spent,
    budgetStart := (← IO.getNumHeartbeats), budgetExcludedStart := (← spent.get)}
  withTheReader Core.Context (fun reader => {reader with maxHeartbeats := 0}) do
    let result ← reconstructExpression ctx owner type
    checkReconstructionBudget ctx
    unless !result.hasFVar && !result.hasMVar do
      throwError "search.statement_not_closed: {owner}"
    let own := (← IO.getNumHeartbeats) - ctx.budgetStart -
      ((← spent.get) - ctx.budgetExcludedStart)
    spent.modify (· + own)
    return result

def copyStatement (source : Environment) (owner : Name) (type : Expr) : MetaM Expr :=
  transportStatement {source} owner type

/-- The import and witness-export paths use the same reconstruction kernel. -/
def copyVocabulary (source : Environment) (n : Name) (visiting : NameSet := {}) : MetaM Unit :=
  transportVocabulary {source, visiting} n

end LeanInformationAudit.SearchReduction
