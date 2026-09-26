import LeanInformationAudit.Registry.Enrollment

namespace LeanInformationAudit.SourceScope
open Lean Meta TemplateAudit

abbrev M := StateT Nat MetaM

def debit (n : Nat := 1) : M Unit := do
  Core.checkMaxHeartbeats "source-bound family"
  unless n ≤ (← get) do throwError "incomplete_closure:E8.source_work"
  modify (· - n)

/-- A dependency-closed coordinate projection and its inverse, preserving raw syntax. -/
partial def project (slots : Array Nat) (scope : Nat) (e : Expr)
    (inverse : Bool := false) (localDepth : Nat := 0) (depth : Nat := 0) : M Expr := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.source_depth"
  let child := fun x => project slots scope x inverse localDepth (depth + 1)
  let bound := fun x => project slots scope x inverse (localDepth + 1) (depth + 1)
  match e with
  | .bvar i =>
    if i < localDepth then return e
    let i := i - localDepth
    if inverse then
      unless i < slots.size do throwError "unclassified_form:source.coordinate_inverse"
      return .bvar (localDepth + scope - 1 - slots[slots.size - 1 - i]!)
    unless i < scope do throwError "unclassified_form:source.open_coordinate"
    let ordinal := scope - 1 - i
    let some index := slots.idxOf? ordinal
      | throwError "unclassified_form:source.coordinate_dependency"
    return .bvar (localDepth + slots.size - 1 - index)
  | .app f a => return .app (← child f) (← child a)
  | .lam n t b bi => return .lam n (← child t) (← bound b) bi
  | .forallE n t b bi => return .forallE n (← child t) (← bound b) bi
  | .letE n t v b nd => return .letE n (← child t) (← child v) (← bound b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ | .fvar _ => throwError "unclassified_form:source.open_expression"
  | _ => return e

def atPath (source : Expr) (path : Array String) : M (Array SourceBinder × Expr) := do
  if path.size > 256 then throwError "incomplete_closure:E8.source_path"
  let mut e := source
  let mut context := #[]
  for step in path do
    debit
    e ← match e, step with
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | .forallE _ d _ _, "domain" | .lam _ d _ _, "domain" => pure d
      | .forallE n d b bi, "body" =>
        context := context.push { name := n, info := bi, domain := d }
        pure b
      | .lam n d b bi, "body" =>
        context := context.push { name := n, info := bi, domain := d, isLambda := true }
        pure b
      | .letE _ t _ _ _, "type" => pure t
      | .letE _ _ v _ _, "value" => pure v
      | .letE n t v b nd, "body" =>
        context := context.push { name := n, info := .default, domain := t, value := some v, nondep := nd }
        pure b
      | .proj _ _ b, "body" | .mdata _ b, "body" => pure b
      | _, _ => throwError "unclassified_form:source.absent_occurrence"
  return (context, e)

partial def inContext (context : Array SourceBinder) (k : Array Expr → M α)
    (i : Nat := 0) (locals : Array Expr := #[]) : M α := do
  debit
  if i == context.size then return ← k locals
  let b := context[i]!
  let domain := b.domain.instantiateRev locals
  fun fuel => do
    let enter := fun x => (inContext context k (i + 1) (locals.push x)).run fuel
    if let some v := b.value then withLetDecl b.name domain (v.instantiateRev locals) enter
    else withLocalDecl b.name b.info domain enter

structure ReadoutScope where
  context : Array SourceBinder
  observation : Expr
  state : Expr
  output : Expr
  projected : Expr

structure Scope where
  source : Expr
  levels : List Name
  selection : SourceSelection
  telescope : Array SourceBinder
  coordinates : Array SourceBinder
  readouts : Array ReadoutScope

private partial def dictionary (type : Expr) : MetaM Bool := do
  let type ← withTransparency .all <| whnf type
  forallTelescope type fun _ result => do
    pure (Lean.isClass (← getEnv) (result.getAppFn.constName?.getD .anonymous))

def resolve (info : ConstantInfo) (selection : SourceSelection) : M Scope := do
  unless info.isTheorem do throwError "unclassified_form:source.theorem"
  let owner := (RegistrationReifier.declaringModuleOf (← getEnv) info.name).getD
    (← getEnv).header.mainModule
  unless selection.owner == owner do throwError "unclassified_form:source.owner"
  let mut telescope := #[]
  let mut e := info.type
  while let .forallE n d b bi := e do
    debit
    if telescope.size ≥ 64 then throwError "incomplete_closure:E8.source_binders"
    telescope := telescope.push { name := n, info := bi, domain := d : SourceBinder }
    e := b
  let slots := selection.coordinates
  if slots.size > 64 || selection.readouts.isEmpty || selection.readouts.size > 64 then
    throwError "unclassified_form:source.selection_size"
  if (selection.readouts.map (·.path)).toList.eraseDups.length != selection.readouts.size then
    throwError "unclassified_form:source.duplicate_occurrence"
  let mut previous : Option Nat := none
  let mut coordinates := #[]
  for i in slots do
    debit
    unless i < telescope.size && previous.all (· < i) do
      throwError "unclassified_form:source.coordinate_order"
    let b := telescope[i]!
    inContext (telescope.extract 0 i) fun locals => do
      let domain := b.domain.instantiateRev locals
      if b.info == .instImplicit || domain == mkSort .zero ||
          (← isProp domain) || (← dictionary domain) then
        throwError "unclassified_form:source.dictionary_or_proof_coordinate"
    let domain ← project (slots.filter (· < i)) i b.domain
    coordinates := coordinates.push { b with domain }
    previous := some i
  let readouts ← selection.readouts.mapM fun selected => do
    let (context, observation) ← atPath info.type selected.path
    for i in slots do
      unless selected.path.size > i &&
          (selected.path.extract 0 (i + 1)).all (· == "body") &&
          context[i]? == telescope[i]? do
        throwError "unclassified_form:source.captured_coordinate"
    unless selected.stateBinder < context.size && slots.all (· < selected.stateBinder) do
      throwError "unclassified_form:source.state_binder"
    let stateBinder := context[selected.stateBinder]!
    if stateBinder.value.isSome then throwError "unclassified_form:source.let_state"
    let output ← inContext context fun locals => do
      let term := observation.instantiateRev locals
      unless !(← isProof term) && !(← isType term) do
        throwError "unclassified_form:source.observation_data"
      return (← inferType term).abstract locals
    let output ← project slots context.size output
    let state ← project slots selected.stateBinder stateBinder.domain
    let projected ← project (slots.push selected.stateBinder) context.size observation
    unless (← project (slots.push selected.stateBinder) context.size projected true).equal observation do
      throwError "unclassified_form:source.inverse_mapping"
    return { context, observation, state, output, projected : ReadoutScope }
  return { source := info.type, levels := info.levelParams, selection, telescope, coordinates, readouts }

private partial def packedType (domains : Array SourceBinder) (i : Nat)
    (parameters : Array Expr) : M Expr := do
  debit
  if i ≥ domains.size then return mkConst ``Unit
  let b := domains[i]!
  let domain := b.domain.instantiateRev parameters
  if i + 1 == domains.size then return domain
  fun fuel => withLocalDecl b.name b.info domain fun x => (do
    let tail ← packedType domains (i + 1) (parameters.push x)
    mkAppM ``Sigma #[← mkLambdaFVars #[x] tail]).run fuel

private partial def packedValue (type : Expr) (parameters : Array Expr) (i : Nat) : M Expr := do
  debit
  if i ≥ parameters.size then return mkConst ``Unit.unit
  if i + 1 == parameters.size then return parameters[i]!
  let args := type.getAppArgs
  unless type.isAppOfArity ``Sigma 2 do throwError "unclassified_form:source.packing"
  let tailType ← whnf (mkApp args[1]! parameters[i]!)
  mkAppOptM ``Sigma.mk #[some args[0]!, some args[1]!, some parameters[i]!,
    some (← packedValue tailType parameters (i + 1))]

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Every selected role is checked at the actual source occurrence and its type.
Coordinate projection is inverted before this kernel equality is used. -/
def validateFields (scope : Scope) (signature actual : Expr) : M Unit := do
  let params ← packedType scope.coordinates 0 #[]
  unless ← isDefEq params (← mkAppM (family ++ `Signature.Params) #[signature]) do
    throwError "unclassified_form:source.params"
  let roles ← RegistrationGates.indices
    (← mkAppM (family ++ `Signature.Role) #[signature])
    (← mkAppM (family ++ `Signature.finiteRole) #[signature])
  unless roles.size == scope.readouts.size do throwError "unclassified_form:source.roles"
  inContext scope.coordinates fun locals => do
    let parameter ← packedValue params locals 0
    for (role, readout) in roles.zip scope.readouts do
      debit
      let state := readout.state.instantiateRev locals
      let output := readout.output.instantiateRev locals
      checkWithKernel state
      checkWithKernel output
      unless (← isType state) && (← isType output) &&
          (← isDefEq state (← mkAppM (family ++ `Signature.State) #[signature, parameter])) &&
          (← isDefEq output (← mkAppM (family ++ `Signature.Output) #[signature, role, parameter])) do
        throwError "unclassified_form:source.state_or_output"
      let observation := Expr.lam `state readout.state readout.projected .default
      let observation := observation.instantiateRev locals
      let actualReadout ← mkAppM (family ++ `Realization.readout) #[actual, role, parameter]
      unless ← isDefEq observation actualReadout do
        throwError "unclassified_form:source.actual_observation"

/-- Definitional reconstruction checks every hypothesis, dictionary and conclusion.
BinderInfo is checked explicitly since Lean defeq alone ignores it. -/
partial def reconstruct (source law : Expr) (depth : Nat := 0) : M Unit := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.reconstruction_depth"
  let law ← whnf law
  match source, law with
  | .forallE n d b bi, .forallE _ d' b' bi' =>
    unless bi == bi' do
      throwError "unclassified_form:source.telescope_reconstruction"
    reconstruct d d' (depth + 1)
    fun fuel => withLocalDecl n bi d fun x =>
      (reconstruct (b.instantiate1 x) (b'.instantiate1 x) (depth + 1)).run fuel
  | .forallE .., _ => throwError "unclassified_form:source.missing_binder"
  | .lam n d b bi, .lam _ d' b' bi' =>
    unless bi == bi' do throwError "unclassified_form:source.lambda_reconstruction"
    reconstruct d d' (depth + 1)
    fun fuel => withLocalDecl n bi d fun x =>
      (reconstruct (b.instantiate1 x) (b'.instantiate1 x) (depth + 1)).run fuel
  | _, _ =>
    unless ← isDefEq source law do throwError "unclassified_form:source.statement_reconstruction"
    -- Inspect logical clauses without interpreting their mathematical operands.
    -- In particular defeq must not erase binder modes below a conjunction or Exists.
    if #[``And, ``Or, ``Iff, ``Not, ``Exists].contains (source.getAppFn.constName?.getD .anonymous) &&
        source.getAppFn == law.getAppFn && source.getAppNumArgs == law.getAppNumArgs then
      for (left, right) in source.getAppArgs.zip law.getAppArgs do
        reconstruct left right (depth + 1)

end LeanInformationAudit.SourceScope
