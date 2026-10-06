import LeanInformationAudit.CompiledSourceScope

namespace LeanInformationAudit.CompiledSourceOperands
open Lean RegistrationGates
abbrev Context := CompiledSourceScope.Context

private def fail [Monad m] [MonadLiftT IO m] (reason : String) : m α :=
  liftM (m := IO) (throw (IO.userError reason) : IO α)

private def getConstInfo (name : Name) : ReaderT Context IO ConstantInfo := do
  let some info := (← read).provenance.view.find? name
    | fail s!"incomplete_closure:E7.compiled_constant:{name}"
  return info

private structure State where
  identity : WalkState
  visited : Std.HashSet Expr := {}
  declarations : Std.HashSet (Name × List Level) := {}
  source : NameSet := {}
  remaining : Nat

private abbrev M := StateT State (ReaderT Context IO)
private def debit : M Unit := do
  let context := (← read).provenance
  if context.heartbeatLimit != 0 &&
      (← IO.getNumHeartbeats) - context.heartbeatStart > context.heartbeatLimit then
    fail "incomplete_closure:E8.source_operand_heartbeats"
  unless (← get).remaining > 0 do fail "incomplete_closure:E8.source_operands"
  modify fun s => { s with remaining := s.remaining - 1 }

private def typeQuery (action : RegistrationGates.QueryM α)
    (operation : String := "type_shape") : M α := do
  let (value, work) ← try
    (RegistrationGates.boundQueryWork action (← get).remaining).run (← read).provenance
  catch error => fail s!"{error}; source_query={operation}; remaining={(← get).remaining}"
  modify fun state => { state with remaining := state.remaining - work }
  return value

private def withLocal (name : Name) (bi : BinderInfo) (type : Expr)
    (value : Option Expr) (body : Expr → M α) (nondep : Bool := false) : M α := do
  let locals := (← read).provenance.locals
  let mut index := (← get).identity.nextLocal
  while locals.contains ⟨Name.num `compiledOperandLocal index⟩ do index := index + 1
  modify fun s => { s with identity := { s.identity with nextLocal := index + 1 } }
  let id : FVarId := ⟨Name.num `compiledOperandLocal index⟩
  let locals := match value with
    | none => locals.mkLocalDecl id name type bi
    | some value => locals.mkLetDecl id name type value nondep
  withReader (fun context : Context => { context with provenance :=
    { context.provenance with locals } }) (body (mkFVar id))

/-- Source operands are compiler declarations reached from the raw statement and
their types. Only repository data bodies are unfolded for this inventory. -/
private def sourceNames (statement : Expr) (fuel : Nat) : ReaderT Context IO (NameSet × Nat) := do
  let view := (← read).provenance.view
  let mut pending := statement.getUsedConstants.toList
  let mut found : NameSet := {}
  let mut remaining := fuel
  while let n :: rest := pending do
    pending := rest
    if found.contains n then continue
    unless remaining > 0 do fail "incomplete_closure:E8.source_inventory"
    remaining := remaining - 1
    found := found.insert n
    let some info := view.find? n
      | fail s!"incomplete_closure:E7.compiled_constant:{n}"
    let some owner := view.ownerOf n
      | fail s!"incomplete_closure:E7.compiled_owner:{n}"
    let (type, work) ← (RegistrationGates.eraseBoundProofs info.type remaining).run (← read).provenance
    remaining := remaining - work
    pending := type.getUsedConstants.toList ++ pending
    if (`D5).isPrefixOf owner && !info.isTheorem then
      if let some value := info.value? then
        let (value, work) ← (RegistrationGates.eraseBoundProofs value remaining).run (← read).provenance
        remaining := remaining - work
        pending := value.getUsedConstants.toList ++ pending
  return (found, remaining)

private partial def visit (e : Expr) (depth : Nat := 0)
    (varyingLaw : Option Expr := none) (lawBody : Option Expr := none) : M Unit := do
  try visitCore e depth varyingLaw lawBody
  catch error =>
    if error.toString.contains "source_operand=" then throw error
    fail s!"{error}; source_operand={e.getAppFn.constName?.getD .anonymous}"

where visitCore (e : Expr) (depth : Nat) (varyingLaw lawBody : Option Expr) : M Unit := do
  debit
  if depth > 256 then fail "incomplete_closure:E8.source_operand_depth"
  if (← get).visited.contains e then return
  modify fun s => { s with visited := s.visited.insert e }
  let state ← get
  let env := (← read).provenance.view
  -- Identity is checked before proof erasure. Apartness requires explicit exact
  -- facts; the varying Law retains its independently bound exclusion route.
  let (_, identity) ← ((RegistrationGates.Compiled.argumentIdentityNode env e).run
    state.identity).run (← read).provenance
  if identity.forbidden then fail "forbidden_dependency:source.operand_identity"
  if identity.incomplete then
    (← read).provenance.trace s!"source operand incomplete remaining={(← get).remaining}; \
      identity_remaining={identity.exprFuel}; expression={repr e}"
    fail "incomplete_closure:source.operand_identity"
  let identity ← if identity.unclassified.isSome then do
      -- The finite grammar can leave an opaque source proposition undecided.
      -- Compiled shape comparison settles only statement identity; it grants no
      -- readout/source correspondence (checked independently by SourceScope).
      let type ← typeQuery (RegistrationGates.typedNodeType e)
      let candidate ← if type == mkSort .zero then pure e
        else if ← typeQuery (RegistrationGates.typedNodeProp type) "proposition" then pure type
        else fail s!"incomplete_closure:source.operand_identity:{repr e}; type={repr type}"
      if candidate.hasMVar || candidate.hasLevelMVar then
        fail "incomplete_closure:source.identity_metavariable"
      let same ← try
        if candidate.hasFVar && lawBody.any (candidate.equal ·) then pure false
        else
          let leftMatch ← typeQuery (RegistrationGates.exactNodeHead? candidate) "exact_candidate"
          let rightMatch ← typeQuery (RegistrationGates.exactNodeHead? identity.statement) "exact_statement"
          let left := leftMatch.getD candidate
          let right := rightMatch.getD identity.statement
          if left.equal right then pure true
          else
            unless leftMatch.isSome && rightMatch.isSome do
              fail "unclassified_form:source.statement_apart_certificate"
            let some leftName := left.getAppFn.constName?
              | fail "unclassified_form:source.statement_apart_certificate"
            let some rightName := right.getAppFn.constName?
              | fail "unclassified_form:source.statement_apart_certificate"
            let some (.inductInfo _) := env.find? leftName
              | fail "unclassified_form:source.statement_apart_certificate"
            let some (.inductInfo _) := env.find? rightName
              | fail "unclassified_form:source.statement_apart_certificate"
            unless leftName != rightName do
              fail "unclassified_form:source.statement_apart_certificate"
            pure false
      catch error =>
        (← read).provenance.trace s!"statement identity failed candidate={repr candidate}; statement={repr identity.statement}"
        throw error
      if same then fail "forbidden_dependency:source.operand_identity"
      pure { identity with unclassified := none }
    else pure identity
  modify fun s => { s with identity }
  -- Proof propositions remain raw dependencies, proof bodies are opaque.
  if ← typeQuery (RegistrationGates.typedNodeProof e) "proof_classification" then
    visit (← typeQuery (RegistrationGates.typedNodeType e)) (depth + 1) varyingLaw lawBody
    return
  let child := fun e => visit e (depth + 1) varyingLaw lawBody
  match e with
  | .app f a => child f; child a
  | .lam n t b bi =>
    child t
    withLocal n bi t none fun x => do
      let body := b.instantiate1 x
      let lawBody := if varyingLaw.any (e.consumeMData.equal ·) then some body else lawBody
      visit body (depth + 1) varyingLaw lawBody
  | .forallE n t b bi =>
    child t
    withLocal n bi t none fun x => child (b.instantiate1 x)
  | .letE n t v b nd =>
    child t
    child v
    withLocal n .default t (some v) (nondep := nd) fun x => child (b.instantiate1 x)
  | .mdata _ b | .proj _ _ b => child b
  | .const name levels =>
    if (← get).declarations.contains (name, levels) then return
    modify fun s => { s with declarations := s.declarations.insert (name, levels) }
    let info ← getConstInfo name
    if info.isUnsafe || (← read).implementedBy name ||
        (← read).extern name then
      fail s!"forbidden_dependency:source.unsafe_or_external:{name}"
    if (← get).source.contains name then return
    if ((← read).provenance.view.getProjectionFnInfo? name).isSome then return
    -- A transparent alias supplies no authority: inspect its raw type and
    -- data body, including recursive declaration references, once per name.
    -- Only the previously resolved source operands are opaque mathematical leaves.
    withReader (fun context : Context => { context with provenance :=
      { context.provenance with locals := {} } }) do
      match info with
      | .inductInfo inductiveInfo =>
        child (Contract.Literal.instantiateRawLevels info.levelParams levels info.type)
        -- A discarded carrier can still carry a whole-statement decision in a field.
        -- Constructor types are data dependencies, even if no constructor is applied.
        for constructor in inductiveInfo.ctors do
          let ctor ← getConstInfo constructor
          child (Contract.Literal.instantiateRawLevels ctor.levelParams levels ctor.type)
      | .ctorInfo _ | .recInfo _ | .quotInfo _ =>
        child (Contract.Literal.instantiateRawLevels info.levelParams levels info.type)
      | .defnInfo definition =>
        child (Contract.Literal.instantiateRawLevels info.levelParams levels info.type)
        child (Contract.Literal.instantiateRawLevels info.levelParams levels definition.value)
      | _ => fail s!"unclassified_form:source.unlinked_operand:{name}"
  | .mvar _ | .bvar _ => fail "unclassified_form:source.open_operand"
  | _ => pure ()

/-- Source linkage supplies the positive operand rule; the existing identity
rejection machinery is applied before any reduction or proof erasure. -/
def check (theoremName : Name) (expressions : Array Expr) (fuel : Nat)
    (law : Option (Expr × Expr) := none) (sourceDefinition : Option Expr := none)
    (checkedFiniteArena : Option Expr := none)
    (exclusion : Option Name := none) (levels : Option (List Level) := none) :
    ReaderT Context IO (Array Name × Nat) := do
  let limit := min 524288 fuel
  let theoremInfo ← getConstInfo theoremName
  let theoremType := match levels with
    | none => theoremInfo.type
    | some levels => Contract.Literal.instantiateRawLevels theoremInfo.levelParams levels theoremInfo.type
  -- Read the law from the same compiler-checked dependent Registration whose
  -- Variation field certifies nonconstancy. A caller-supplied law must match
  -- that complete field; no proof body or evaluation supplies this authority.
  let (varyingLaw, available) ← match law with
    | none => pure (none, limit)
    | some (record, observed) => do
      let some exclusion := exclusion | fail "unclassified_form:source.exclusion_missing"
      let context ← read
      let view := context.provenance.view
      let certificate ← getConstInfo exclusion
      discard <| IO.ofExcept <| Contract.NodeFacts.exclusion {
        find := view.find?, owner := view.ownerOf,
        external := context.extern } exclusion
      unless certificate.type.getAppArgs[2]!.equal theoremType do
        fail "contract.node_binding:source.exclusion_statement"
      let action : CompiledSourceScope.M (Option Expr) := do
        unless record.isConst do fail "unclassified_form:source.variation_record"
        let type ← CompiledSourceScope.projectType record
        let family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily
        unless type.isAppOfArity (family ++ `Registration) 2 do
          fail "unclassified_form:source.variation_record"
        let expected ← CompiledSourceScope.normalizeHead
          (← CompiledSourceScope.projectField (family ++ `Arena.Law) type.getAppArgs[0]!)
        let observed ← CompiledSourceScope.normalizeHead observed
        unless (← CompiledSourceScope.normalizeHead certificate.type.getAppArgs[1]!).equal observed do
          fail "contract.node_binding:source.exclusion_law"
        unless expected.isLambda && expected.equal observed do
          fail "unclassified_form:source.variation_law"
        return some expected
      action.run limit
  let identity ← (RegistrationGates.Compiled.argumentIdentityState theoremName available levels).run (← read).provenance
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
  (← read).provenance.trace s!"source operand inventory names={source.size}; \
    remaining={remaining}; initial={limit}; identity_remaining={identity.exprFuel}"
  let action : M Unit := do
    for e in expressions do visit e (varyingLaw := varyingLaw)
    if let some (_, law) := law then visit law (varyingLaw := varyingLaw)
  let (_, state) ← action.run { identity := { identity with exprFuel := remaining }, source, remaining }
  let used := (remaining - state.remaining) + (remaining - state.identity.exprFuel)
  unless used ≤ remaining do fail "incomplete_closure:E8.source_operand_work"
  (← read).provenance.trace s!"source operands source_names={source.size} \
    raw_visits={remaining - state.remaining} unique_expr={state.visited.size} \
    repeated={remaining - state.remaining - state.visited.size} \
    declarations={state.declarations.size} work={limit - remaining + used}"
  return (state.declarations.toArray.map (·.1), limit - remaining + used)


end LeanInformationAudit.CompiledSourceOperands
