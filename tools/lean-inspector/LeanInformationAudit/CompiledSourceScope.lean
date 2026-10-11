import LeanInformationAudit.TemplateEnrollment
import LeanInformationAudit.Registry.SourceBinder

namespace LeanInformationAudit.CompiledSourceScope
open Lean

/-- Source checks operate on compiler syntax with an explicit lexical context. -/
abbrev Context := TemplateAudit.CompiledEnrollment.Context
abbrev M := StateT Nat (ReaderT Context IO)

private def fail [Monad m] [MonadLiftT IO m] (reason : String) : m α :=
  liftM (m := IO) (throw (IO.userError reason) : IO α)

def debit (n : Nat := 1) : M Unit := do
  let context := (← read).provenance
  if context.heartbeatLimit != 0 &&
      (← IO.getNumHeartbeats) - context.heartbeatStart > context.heartbeatLimit then
    fail "incomplete_closure:E8.source_heartbeats"
  unless n ≤ (← get) do fail "incomplete_closure:E8.source_work"
  modify (· - n)

def query (action : Contract.CompiledExpressions.M α) : M α := do
  let (value, work) ← (RegistrationGates.compiledQueryWork action (← get)).run
    (← read).provenance
  debit work
  return value

def getConstInfo (name : Name) : M ConstantInfo := do
  debit
  let some info := (← read).provenance.view.find? name
    | fail s!"incomplete_closure:E7.compiled_constant:{name}"
  return info

def ownerOf (name : Name) : M Name := do
  let some owner := (← read).provenance.view.ownerOf name
    | fail s!"incomplete_closure:E7.compiled_owner:{name}"
  return owner

def projectType (e : Expr) : M Expr := query (Contract.CompiledExpressions.typeShape e)
def isType (e : Expr) : M Bool := do
  return (← query (Contract.CompiledExpressions.head (← projectType e))).isSort

def isProp (e : Expr) : M Bool := query (Contract.CompiledExpressions.propositionShape e)
def isProof (e : Expr) : M Bool := do isProp (← projectType e)
def normalizeHead (e : Expr) : M Expr := query (Contract.CompiledExpressions.head e)
def sameShape (a b : Expr) : M Bool := query (Contract.CompiledExpressions.sameShape a b)

def withLocal (name : Name) (bi : BinderInfo) (type : Expr)
    (value : Option Expr) (body : Expr → M α) : M α := do
  debit
  let locals := (← read).provenance.locals
  let mut index := locals.numIndices
  while locals.contains ⟨Name.num `compiledSourceLocal index⟩ do index := index + 1
  let id : FVarId := ⟨Name.num `compiledSourceLocal index⟩
  let locals := match value with
    | none => locals.mkLocalDecl id name type bi
    | some value => locals.mkLetDecl id name type value
  withReader (fun context : Context => { context with provenance :=
    { context.provenance with locals } }) (body (mkFVar id))

private def withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr)
    (body : Expr → M α) : M α := withLocal name bi type none body
private def withLocalDeclD (name : Name) (type : Expr) (body : Expr → M α) : M α :=
  withLocalDecl name .default type body
private def withLetDecl (name : Name) (type value : Expr) (body : Expr → M α) : M α :=
  withLocal name .default type (some value) body

/-- Named record projections use only their compiled layout. The base and
explicit field arguments are existing checked terms. -/
def projectField (name : Name) (base : Expr) (arguments : Array Expr := #[]) : M Expr := do
  debit
  let some projection := (← read).provenance.view.getProjectionFnInfo? name
    | fail s!"incomplete_closure:E7.compiled_projection:{name}"
  let .ctorInfo ctor ← getConstInfo projection.ctorName
    | fail s!"incomplete_closure:E7.compiled_constructor:{projection.ctorName}"
  return mkAppN (.proj ctor.induct projection.i base) arguments

private def typeLevel (type : Expr) : M Level := do
  let .sort sort ← normalizeHead (← projectType type)
    | fail "unclassified_form:source.packing_sort"
  let some level := sort.dec | fail "unclassified_form:source.packing_sort"
  return level

private def mkLambdaFVars (xs : Array Expr) (body : Expr) : M Expr := do
  let mut body := body
  for x in xs.reverse do
    let some binder := (← read).provenance.locals.find? x.fvarId!
      | fail "incomplete_closure:E7.compiled_local"
    body := .lam binder.userName binder.type (body.abstract #[x]) binder.binderInfo
  return body

/-- Predicate reification is symbolic. Its decision dictionary is not executed
or synthesized; the comparison recognizes the proposition of a compiled decide. -/
private def mkDecide (proposition : Expr) : M Expr := do
  debit
  return mkApp2 (mkConst ``Decidable.decide) proposition
    (mkApp (mkConst ``Classical.propDecidable) proposition)

private def mkEq (left right : Expr) : M Expr := do
  debit
  return mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Bool) left right

/-- A dependency-closed coordinate projection and its inverse, preserving raw syntax. -/
partial def project (slots : Array Nat) (scope : Nat) (e : Expr)
    (inverse : Bool := false) (localDepth : Nat := 0) (depth : Nat := 0) : M Expr := do
  debit
  if depth > 256 then fail "incomplete_closure:E8.source_depth"
  let child := fun x => project slots scope x inverse localDepth (depth + 1)
  let bound := fun x => project slots scope x inverse (localDepth + 1) (depth + 1)
  match e with
  | .bvar i =>
    if i < localDepth then return e
    let i := i - localDepth
    if inverse then
      unless i < slots.size do fail "unclassified_form:source.coordinate_inverse"
      return .bvar (localDepth + scope - 1 - slots[slots.size - 1 - i]!)
    unless i < scope do fail "unclassified_form:source.open_coordinate"
    let ordinal := scope - 1 - i
    let some index := slots.idxOf? ordinal
      | fail s!"unclassified_form:source.coordinate_dependency:missing={ordinal};selected={slots};scope={scope}"
    return .bvar (localDepth + slots.size - 1 - index)
  | .app f a => return .app (← child f) (← child a)
  | .lam n t b bi => return .lam n (← child t) (← bound b) bi
  | .forallE n t b bi => return .forallE n (← child t) (← bound b) bi
  | .letE n t v b nd => return .letE n (← child t) (← child v) (← bound b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ | .fvar _ => fail "unclassified_form:source.open_expression"
  | _ => return e

/-- Expand only lexical let references, from their original raw values. The target
scope stays fixed while a value is interpreted in its strictly earlier context.
`extraDepth` lifts free coordinates under the occurrence's internal binders;
new binders inside the value keep their own de Bruijn indices. No definitions,
proofs or dictionaries become independently variable parameters. -/
partial def expandLets (context : Array SourceBinder) (scope : Nat) (e : Expr)
    (localDepth : Nat := 0) (extraDepth : Nat := 0) (depth : Nat := 0) : M Expr := do
  debit
  if depth > 256 then fail "incomplete_closure:E8.source_depth"
  let child := fun x => expandLets context scope x localDepth extraDepth (depth + 1)
  let bound := fun x => expandLets context scope x (localDepth + 1) extraDepth (depth + 1)
  match e with
  | .bvar i =>
    if i < localDepth then return e
    let i := i - localDepth
    unless i < context.size do fail "unclassified_form:source.open_coordinate"
    let ordinal := context.size - 1 - i
    if let some value := context[ordinal]!.value then
      return ← expandLets (context.extract 0 ordinal) scope value 0
        (localDepth + extraDepth) (depth + 1)
    return .bvar (localDepth + extraDepth + scope - 1 - ordinal)
  | .app f a => return .app (← child f) (← child a)
  | .lam n t b bi => return .lam n (← child t) (← bound b) bi
  | .forallE n t b bi => return .forallE n (← child t) (← bound b) bi
  | .letE n t v b nd => return .letE n (← child t) (← child v) (← bound b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ | .fvar _ => fail "unclassified_form:source.open_expression"
  | _ => return e

/-- Capture-avoiding projection with a raw inverse check after source-determined
local-let transport. Apply to domains and outputs as well as observations. -/
def transport (context : Array SourceBinder) (slots : Array Nat) (e : Expr) : M Expr := do
  let expanded ← expandLets context context.size e
  let projected ← try project slots context.size expanded catch error =>
    (← read).provenance.trace s!"coordinate dependency expression={repr expanded}; \
      binders={repr (context.map fun b => (b.name, b.domain, b.value))}"
    throw error
  unless (← project slots context.size projected true).equal expanded do
    fail "unclassified_form:source.inverse_mapping"
  return projected

def atPath (source : Expr) (path : Array String) : M (Array SourceBinder × Expr) := do
  if path.size > 256 then fail "incomplete_closure:E8.source_path"
  let mut e := source
  let mut context := #[]
  let mut anchorPath := #[]
  for step in path do
    debit
    anchorPath := anchorPath.push step
    e ← match e, step with
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | .forallE _ d _ _, "domain" | .lam _ d _ _, "domain" => pure d
      | .forallE n d b bi, "body" =>
        context := context.push { path := anchorPath, name := n, info := bi, domain := d }
        pure b
      | .lam n d b bi, "body" =>
        context := context.push { path := anchorPath, name := n, info := bi, domain := d, isLambda := true }
        pure b
      | .letE _ t _ _ _, "type" => pure t
      | .letE _ _ v _ _, "value" => pure v
      | .letE n t v b nd, "body" =>
        context := context.push {
          path := anchorPath, name := n, info := .default,
          domain := t, value := some v, nondep := nd }
        pure b
      | .proj _ _ b, "body" | .mdata _ b, "body" => pure b
      | _, _ => fail "unclassified_form:source.absent_occurrence"
  return (context, e)

/-- Replace one explicit raw occurrence, without entering definitions or binders. -/
partial def replaceAt (e : Expr) (path : List String) (value : Expr) : M Expr := do
  debit
  match path, e with
  | [], _ => return value
  | "fn" :: rest, .app f a => return .app (← replaceAt f rest value) a
  | "arg" :: rest, .app f a => return .app f (← replaceAt a rest value)
  | _, _ => fail "unclassified_form:source.state_operand_path"

/-- Rebuild one admitted source occurrence in its original lexical context.
The replacement already uses that context's de Bruijn coordinates; surrounding
binders and untouched fields retain their raw syntax without shifting. -/
partial def replaceSourceAt (e : Expr) (path : List String) (value : Expr)
    (depth : Nat := 0) : M Expr := do
  debit
  if depth > 256 then fail "incomplete_closure:E8.source_path"
  let child := fun e rest => replaceSourceAt e rest value (depth + 1)
  match path, e with
  | [], _ => return value
  | "fn" :: rest, .app f a => return .app (← child f rest) a
  | "arg" :: rest, .app f a => return .app f (← child a rest)
  | "domain" :: rest, .forallE n d b bi => return .forallE n (← child d rest) b bi
  | "body" :: rest, .forallE n d b bi => return .forallE n d (← child b rest) bi
  | "domain" :: rest, .lam n d b bi => return .lam n (← child d rest) b bi
  | "body" :: rest, .lam n d b bi => return .lam n d (← child b rest) bi
  | "type" :: rest, .letE n t v b nd => return .letE n (← child t rest) v b nd
  | "value" :: rest, .letE n t v b nd => return .letE n t (← child v rest) b nd
  | "body" :: rest, .letE n t v b nd => return .letE n t v (← child b rest) nd
  | "body" :: rest, .proj n i b => return .proj n i (← child b rest)
  | "body" :: rest, .mdata m b => return .mdata m (← child b rest)
  | _, _ => fail "unclassified_form:source.absent_occurrence"

partial def inContext (context : Array SourceBinder) (k : Array Expr → M α)
    (i : Nat := 0) (locals : Array Expr := #[]) : M α := do
  debit
  if i == context.size then return ← k locals
  let b := context[i]!
  let domain := b.domain.instantiateRev locals
  withLocal b.name b.info domain (b.value.map (·.instantiateRev locals)) fun x =>
    inContext context k (i + 1) (locals.push x)

structure ReadoutScope where
  context : Array SourceBinder
  observation : Expr
  state : Expr
  output : Expr
  projected : Expr
  rawContext : Array SourceBinder := #[]
  rawObservation : Expr := default

structure DefinitionEntry where
  path : Array String
  owner : Name
  name : Name
  type : Expr
  value : Expr

structure Scope where
  /-- The theorem's raw type remains the binding root even when a named claim
  definition is entered for lexical source observations. -/
  source : Expr
  /-- One-step replacement preserves the surrounding raw theorem structure. -/
  expanded : Expr
  definition : Option DefinitionEntry
  levels : List Name
  selection : SourceSelection
  telescope : Array SourceBinder
  coordinates : Array SourceBinder
  readouts : Array ReadoutScope

private partial def dictionary (type : Expr) : M Bool := do
  let type ← normalizeHead type
  match type with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => dictionary (b.instantiate1 x)
  | _ => return (← read).provenance.view.isClass (type.getAppFn.constName?.getD .anonymous)

def resolve (info : ConstantInfo) (selection : SourceSelection)
    (universeArguments : List Level := info.levelParams.map Level.param) : M Scope := do
  unless info.isTheorem do fail "unclassified_form:source.theorem"
  let owner ← ownerOf info.name
  unless selection.owner == owner do fail "unclassified_form:source.owner"
  let definition : Option DefinitionEntry ← match selection.definition with
    | none => pure none
    | some selected => do
      unless selected.owner == owner do fail "unclassified_form:source.definition_owner"
      let definitionInfo ← getConstInfo selected.name
      let definitionOwner ← ownerOf selected.name
      unless definitionOwner == owner do
        fail "unclassified_form:source.definition_owner"
      let .defnInfo declaration := definitionInfo
        | fail "unclassified_form:source.definition_kind"
      debit
      if definitionInfo.isUnsafe ||
          (← read).implementedBy selected.name ||
          (← read).extern selected.name then
        fail "forbidden_dependency:source.definition_safety"
      unless definitionInfo.type == mkSort .zero do
        fail "unclassified_form:source.definition_type"
      unless definitionInfo.levelParams.length == universeArguments.length do
        fail "unclassified_form:source.definition_universes"
      let reference := mkConst selected.name universeArguments
      let occurrence ← if selected.path.isEmpty then pure info.type
        else if selected.path == #["arg"] && info.type.isAppOfArity ``Not 1 then
          pure info.type.getAppArgs[0]!
        else fail "unclassified_form:source.definition_path"
      unless occurrence.equal reference do
        fail "unclassified_form:source.definition_reference"
      for readout in selection.readouts do
        unless selected.path.size < readout.path.size &&
            readout.path.extract 0 selected.path.size == selected.path do
          fail "unclassified_form:source.definition_readout_path"
      let value := declaration.value.instantiateLevelParams definitionInfo.levelParams
        universeArguments
      let type := definitionInfo.type.instantiateLevelParams definitionInfo.levelParams
        universeArguments
      pure (some {
        path := selected.path
        owner := definitionOwner
        name := selected.name
        type := type
        value := value })
  let source := match definition with
    | none => info.type
    | some entry => if entry.path.isEmpty then entry.value
      else mkApp info.type.getAppFn entry.value
  let mut telescope := #[]
  let mut e := info.type
  while let .forallE n d b bi := e do
    debit
    if telescope.size ≥ 64 then fail "incomplete_closure:E8.source_binders"
    telescope := telescope.push { name := n, info := bi, domain := d : SourceBinder }
    e := b
  let slots := selection.coordinates
  if slots.size > 64 || selection.readouts.isEmpty || selection.readouts.size > 64 then
    fail "unclassified_form:source.selection_size"
  if (selection.readouts.map (·.path)).toList.eraseDups.length != selection.readouts.size then
    fail "unclassified_form:source.duplicate_occurrence"
  let occurrences ← selection.readouts.mapM fun selected => atPath source selected.path
  let coordinateContext := occurrences[0]!.1
  let mut previous : Option Nat := none
  let mut coordinates := #[]
  for i in slots do
    debit
    unless i < coordinateContext.size && previous.all (· < i) do
      fail "unclassified_form:source.coordinate_order"
    let b := coordinateContext[i]!
    -- Exact source ancestry, never equality of names or binder domains alone.
    for (context, _) in occurrences do
      debit (b.path.size + 1)
      unless context[i]?.any (fun other => other.path == b.path) do
        fail "unclassified_form:source.captured_coordinate"
    inContext (coordinateContext.extract 0 i) fun locals => do
      let domain := b.domain.instantiateRev locals
      if b.info == .instImplicit || domain == mkSort .zero ||
          (← isProp domain) || (← dictionary domain) then
        fail "unclassified_form:source.dictionary_or_proof_coordinate"
    if b.value.isSome then fail "unclassified_form:source.let_coordinate"
    let domain ← transport (coordinateContext.extract 0 i) (slots.filter (· < i)) b.domain
    coordinates := coordinates.push { b with domain }
    previous := some i
  let readouts ← (selection.readouts.zip occurrences).mapM fun (selected, context, observation) => do
    if selected.functionOperand || selected.stateOperand.isSome then
      unless selected.stateBinder == 0 && !(selected.functionOperand && selected.stateOperand.isSome) &&
          !(selected.functionOperand && selected.booleanPredicate) do
        fail "unclassified_form:source.operand_mode"
      let (state, body) ← inContext context fun locals => do
        let term := observation.instantiateRev locals
        if selected.functionOperand then
          let .forallE _ domain output .default := (← projectType term)
            | fail "unclassified_form:source.function_operand"
          unless !output.hasLooseBVars && !(← isProp domain) && !(← isType term) do
            fail "unclassified_form:source.function_operand"
          let typeArgument ← withLocalDeclD `state domain fun state => isType state
          if typeArgument then fail "unclassified_form:source.function_operand"
          return (domain.abstract locals, mkApp (observation.liftLooseBVars 0 1) (.bvar 0))
        else
          let path := selected.stateOperand.get!
          unless !path.isEmpty && path.size ≤ 256 do
            fail "unclassified_form:source.state_operand_path"
          let (inside, operand) ← atPath observation path
          unless inside.isEmpty do fail "unclassified_form:source.state_operand_scope"
          let operand := operand.instantiateRev locals
          unless !(← isProof operand) && !(← isType operand) do
            fail "unclassified_form:source.state_operand_data"
          let state ← projectType operand
          let body ← replaceAt (observation.liftLooseBVars 0 1) path.toList (.bvar 0)
          return (state.abstract locals, body)
      let extended := context.push {name := `state, info := .default, domain := state}
      let body ← if selected.booleanPredicate then
          inContext extended fun locals => do
            let term := body.instantiateRev locals
            unless ← isProp term do fail "unclassified_form:source.boolean_predicate"
            return (← mkDecide term).abstract locals
        else pure body
      let output ← inContext extended fun locals => do
        let term := body.instantiateRev locals
        unless !(← isProof term) && !(← isType term) do
          fail "unclassified_form:source.observation_data"
        return (← projectType term).abstract locals
      let state ← transport context slots state
      let output ← transport extended slots output
      let projected ← transport extended (slots.push context.size) body
      return {
        context := extended
        observation := body
        state, output, projected
        rawContext := context
        rawObservation := observation : ReadoutScope }
    if selected.booleanPredicate then fail "unclassified_form:source.operand_mode"
    unless selected.stateBinder < context.size && slots.all (· < selected.stateBinder) do
      fail "unclassified_form:source.state_binder"
    let stateBinder := context[selected.stateBinder]!
    if stateBinder.value.isSome then fail "unclassified_form:source.let_state"
    let output ← inContext context fun locals => do
      let term := observation.instantiateRev locals
      unless !(← isProof term) && !(← isType term) do
        fail "unclassified_form:source.observation_data"
      return (← projectType term).abstract locals
    let output ← transport context slots output
    let state ← transport (context.extract 0 selected.stateBinder) slots stateBinder.domain
    let projected ← transport context (slots.push selected.stateBinder) observation
    return { context, observation, state, output, projected, rawContext := context, rawObservation := observation : ReadoutScope }
  let mut reconstructedSource := source
  for (selected, context, observation) in selection.readouts.zip occurrences do
    if selected.booleanPredicate then
      let reified ← inContext context fun locals => do
        let term := observation.instantiateRev locals
        unless ← isProp term do fail "unclassified_form:source.boolean_predicate"
        return (← mkEq (← mkDecide term) (mkConst ``Bool.true)).abstract locals
      reconstructedSource ← replaceSourceAt reconstructedSource selected.path.toList reified
  return {
    source := info.type
    expanded := reconstructedSource
    definition := definition
    levels := info.levelParams
    selection := selection
    telescope := telescope
    coordinates := coordinates
    readouts := readouts }

private partial def packedType (domains : Array SourceBinder) (i : Nat)
    (parameters : Array Expr) : M Expr := do
  debit
  if i ≥ domains.size then return mkConst ``Unit
  let b := domains[i]!
  let domain := b.domain.instantiateRev parameters
  if i + 1 == domains.size then return domain
  withLocalDecl b.name b.info domain fun x => do
    let tail ← packedType domains (i + 1) (parameters.push x)
    let u ← typeLevel domain
    let v ← typeLevel tail
    return mkApp2 (mkConst ``Sigma [u, v]) domain (← mkLambdaFVars #[x] tail)

private partial def packedValue (type : Expr) (parameters : Array Expr) (i : Nat) : M Expr := do
  debit
  if i ≥ parameters.size then return mkConst ``Unit.unit
  if i + 1 == parameters.size then return parameters[i]!
  let args := type.getAppArgs
  unless type.isAppOfArity ``Sigma 2 do fail "unclassified_form:source.packing"
  let tailType ← normalizeHead (mkApp args[1]! parameters[i]!)
  return mkApp4 (mkConst ``Sigma.mk type.getAppFn.constLevels!) args[0]! args[1]!
    parameters[i]! (← packedValue tailType parameters (i + 1))

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Every selected role is checked at the actual source occurrence and its type.
Coordinate projection is inverted before compiled shapes are compared. -/
def validateFields (scope : Scope) (signature actual : Expr) : M Unit := do
  let params ← packedType scope.coordinates 0 #[]
  unless ← sameShape params (← projectField (family ++ `Signature.Params) signature) do
    fail "unclassified_form:source.params"
  let roles ← query <| Contract.CompiledExpressions.finiteIndices
    (← projectField (family ++ `Signature.finiteRole) signature)
  unless roles.size == scope.readouts.size do fail "unclassified_form:source.roles"
  inContext scope.coordinates fun locals => do
    let parameter ← packedValue params locals 0
    for (role, readout) in roles.zip scope.readouts do
      debit
      let state := readout.state.instantiateRev locals
      let output := readout.output.instantiateRev locals
      unless (← isType state) && (← isType output) &&
          (← sameShape state (← projectField (family ++ `Signature.State) signature #[parameter])) &&
          (← sameShape output (← projectField (family ++ `Signature.Output) signature #[role, parameter])) do
        fail "unclassified_form:source.state_or_output"
      let observation := Expr.lam `state readout.state readout.projected .default
      let observation := observation.instantiateRev locals
      let actualReadout ← projectField (family ++ `Realization.readout) actual #[role, parameter]
      unless ← sameShape observation actualReadout do
        fail "unclassified_form:source.actual_observation"

/-- Structural reconstruction checks every hypothesis, dictionary and conclusion.
BinderInfo is checked explicitly since Lean defeq alone ignores it. -/
partial def reconstruct (source law : Expr) (depth : Nat := 0) : M Unit := do
  debit
  if depth > 256 then fail "incomplete_closure:E8.reconstruction_depth"
  if source.equal law then return
  let law ← match law with
    | .forallE .. | .lam .. | .letE .. => pure law
    | _ =>
      if !source.isAppOfArity ``Not 1 && source.getAppFn == law.getAppFn then pure law
      else query (Contract.CompiledExpressions.head law (zeta := false))
  -- Head computation exposes Not as an implication. Keep its source polarity and inspect
  -- the full proposition underneath, including all binder modes.
  if source.isAppOfArity ``Not 1 then
    let .forallE _ domain body .default := law
      | fail "unclassified_form:source.statement_reconstruction"
    unless body.equal (mkConst ``False) do
      fail "unclassified_form:source.statement_reconstruction"
    reconstruct source.getAppArgs[0]! domain (depth + 1)
    return
  match source, law with
  | .letE n d v b _, .letE _ d' v' b' _ =>
    reconstruct d d' (depth + 1)
    unless ← sameShape v v' do fail "unclassified_form:source.let_reconstruction"
    withLetDecl n d v fun x =>
      reconstruct (b.instantiate1 x) (b'.instantiate1 x) (depth + 1)
  | .letE .., _ => fail "unclassified_form:source.missing_let"
  | .forallE n d b bi, .forallE _ d' b' bi' =>
    unless bi == bi' do
      fail "unclassified_form:source.telescope_reconstruction"
    reconstruct d d' (depth + 1)
    withLocalDecl n bi d fun x =>
      reconstruct (b.instantiate1 x) (b'.instantiate1 x) (depth + 1)
  | .forallE .., _ => fail "unclassified_form:source.missing_binder"
  | .lam n d b bi, .lam _ d' b' bi' =>
    unless bi == bi' do fail "unclassified_form:source.lambda_reconstruction"
    reconstruct d d' (depth + 1)
    withLocalDecl n bi d fun x =>
      reconstruct (b.instantiate1 x) (b'.instantiate1 x) (depth + 1)
  | _, _ =>
    unless ← sameShape source law do fail "unclassified_form:source.statement_reconstruction"
    -- Inspect logical clauses without interpreting their mathematical operands.
    -- In particular defeq must not erase binder modes below a conjunction or Exists.
    if #[``And, ``Or, ``Iff, ``Not, ``Exists].contains (source.getAppFn.constName?.getD .anonymous) &&
        source.getAppFn == law.getAppFn && source.getAppNumArgs == law.getAppNumArgs then
      for (left, right) in source.getAppArgs.zip law.getAppArgs do
        reconstruct left right (depth + 1)


end LeanInformationAudit.CompiledSourceScope
