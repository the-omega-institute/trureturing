import LeanInformationAudit.Registry.SourceScope

namespace LeanInformationAudit.SourceOperands
open Lean Meta TemplateAudit RegistrationGates

private structure State where
  identity : WalkState
  visited : Std.HashSet Expr := {}
  declarations : Std.HashSet (Name × List Level) := {}
  source : NameSet := {}
  remaining : Nat

private abbrev M := StateT State MetaM
private def debit : M Unit := do
  Core.checkMaxHeartbeats "source operand provenance"
  unless (← get).remaining > 0 do throwError "incomplete_closure:E8.source_operands"
  modify fun s => { s with remaining := s.remaining - 1 }

/-- Source operands are compiler declarations reached from the raw statement and
their types. Only repository data bodies are unfolded for this inventory. -/
private def sourceNames (statement : Expr) (fuel : Nat) : MetaM (NameSet × Nat) := do
  let mut pending := statement.getUsedConstants.toList
  let mut found : NameSet := {}
  let mut remaining := fuel
  while let n :: rest := pending do
    pending := rest
    if found.contains n then continue
    if remaining == 0 then throwError "incomplete_closure:E8.source_dependencies"
    remaining := remaining - 1
    found := found.insert n
    let info ← getConstInfo n
    let owner := (RegistrationReifier.declaringModuleOf (← getEnv) n).getD
      (← getEnv).header.mainModule
    let (type, work) ← eraseProofs info.type remaining
    remaining := remaining - work
    pending := type.getUsedConstants.toList ++ pending
    if (`D5).isPrefixOf owner && !(← isProp info.type) then
      if let some value := info.value? then
        let (value, work) ← eraseProofs value remaining
        remaining := remaining - work
        pending := value.getUsedConstants.toList ++ pending
  return (found, remaining)

private partial def visit (e : Expr) (depth : Nat := 0) : M Unit := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.source_operand_depth"
  if (← get).visited.contains e then return
  modify fun s => { s with visited := s.visited.insert e }
  let state ← get
  let env ← getEnv
  -- This branch already settles rigid proposition identity by Lean conversion
  -- below. Do not first expand the same complete telescope through the legacy
  -- statement-apart grammar. Raw heads, types and dependencies are still checked.
  let (_, identity) ← (argumentIdentityNode env e (deferStatementApart := true)).run state.identity
  if identity.forbidden then throwError "forbidden_dependency:source.operand_identity"
  if identity.incomplete then throwError "incomplete_closure:source.operand_identity:{e}"
  let identity ← if identity.unclassified.isSome then do
      -- The finite grammar can leave an opaque source proposition undecided.
      -- Rigid Lean conversion settles only statement identity; it grants no
      -- readout/source correspondence (checked independently by SourceScope).
      let type ← inferType e
      let candidate ← if type == mkSort .zero then pure e
        else if ← isProp type then pure type
        else throwError "incomplete_closure:source.operand_identity:{e}; type={type}"
      if candidate.hasMVar || candidate.hasLevelMVar then
        throwError "incomplete_closure:source.identity_metavariable"
      if ← withTransparency .all <| isDefEq candidate identity.statement then
        throwError "forbidden_dependency:source.operand_identity"
      pure { identity with unclassified := none }
    else pure identity
  modify fun s => { s with identity }
  -- Proof propositions remain raw dependencies, proof bodies are opaque.
  if ← isProof e then
    visit (← inferType e) (depth + 1)
    return
  let child := fun e => visit e (depth + 1)
  match e with
  | .app f a => child f; child a
  | .lam n t b bi | .forallE n t b bi =>
    child t
    fun s => withLocalDecl n bi t fun x => (child (b.instantiate1 x)).run s
  | .letE n t v b _ =>
    child t
    child v
    fun s => withLetDecl n t v fun x => (child (b.instantiate1 x)).run s
  | .mdata _ b | .proj _ _ b => child b
  | .const name levels =>
    if (← get).declarations.contains (name, levels) then return
    modify fun s => { s with declarations := s.declarations.insert (name, levels) }
    let info ← getConstInfo name
    if info.isUnsafe || (Compiler.getImplementedBy? (← getEnv) name).isSome ||
        (getExternAttrData? (← getEnv) name).isSome then
      throwError "forbidden_dependency:source.unsafe_or_external:{name}"
    if (← get).source.contains name then return
    if ((← getEnv).getProjectionFnInfo? name).isSome then return
    -- A transparent alias supplies no authority: inspect its raw type and
    -- data body, including recursive declaration references, once per name.
    -- Only the previously resolved source operands are opaque mathematical leaves.
    match info with
    | .inductInfo inductiveInfo =>
      child (info.type.instantiateLevelParams info.levelParams levels)
      -- A discarded carrier can still carry a whole-statement decision in a field.
      -- Constructor types are data dependencies, even if no constructor is applied.
      for constructor in inductiveInfo.ctors do
        let ctor ← getConstInfo constructor
        child (ctor.type.instantiateLevelParams ctor.levelParams levels)
    | .ctorInfo _ | .recInfo _ | .quotInfo _ =>
      child (info.type.instantiateLevelParams info.levelParams levels)
    | .defnInfo definition =>
      child (info.type.instantiateLevelParams info.levelParams levels)
      child (definition.value.instantiateLevelParams info.levelParams levels)
    | _ => throwError "unclassified_form:source.unlinked_operand:{name}"
  | .mvar _ | .bvar _ => throwError "unclassified_form:source.open_operand"
  | _ => pure ()

/-- Source linkage supplies the positive operand rule; the existing identity
rejection machinery is applied before any reduction or proof erasure. -/
def check (theoremName : Name) (expressions : Array Expr) (fuel : Nat)
    (law : Option Expr := none) (sourceDefinition : Option Expr := none)
    (checkedFiniteArena : Option Expr := none) : MetaM (Array Name × Nat) := do
  let limit := min 524288 fuel
  let identity ← argumentIdentityState theoremName limit
  let theoremType := (← getConstInfo theoremName).type
  let (source, remaining) ← sourceNames theoremType identity.exprFuel
  let (source, remaining) ← match sourceDefinition with
    | none => pure (source, remaining)
    | some definition => do
      let (definitionSource, remaining) ← sourceNames definition remaining
      pure (definitionSource.toArray.foldl (init := source) (fun acc name => acc.insert name), remaining)
  -- Only SourceContract supplies this after SourceFinite checks the complete
  -- signature, source observations, all-realization Law and original catalog unit.
  -- Its fixed finite dictionaries are source dependencies; arbitrary registration
  -- helpers do not acquire this authority. Unsafe heads still reject before lookup.
  let (source, remaining) ← match checkedFiniteArena with
    | none => pure (source, remaining)
    | some arena => do
      let (arenaSource, remaining) ← sourceNames arena remaining
      pure (arenaSource.toArray.foldl (init := source) (fun acc name => acc.insert name), remaining)
  let action : M Unit := do
    for e in expressions do visit e
    if let some law := law then visit law
  let (_, state) ← action.run { identity := { identity with exprFuel := remaining }, source, remaining }
  let used := (remaining - state.remaining) + (remaining - state.identity.exprFuel)
  unless used ≤ remaining do throwError "incomplete_closure:E8.source_operand_work"
  trace[InformationRegistration.check] "source operands source_names={source.size} raw_visits={remaining - state.remaining} unique_expr={state.visited.size} repeated={remaining - state.remaining - state.visited.size} declarations={state.declarations.size} work={limit - remaining + used}"
  return (state.declarations.toArray.map (·.1), limit - remaining + used)

end LeanInformationAudit.SourceOperands
