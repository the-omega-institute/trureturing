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

def query (action : RegistrationGates.QueryM α) : M α := do
  let (value, work) ← (RegistrationGates.boundQueryWork action (← get)).run
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

def projectType (e : Expr) : M Expr := query (RegistrationGates.typedNodeType e)
def isType (e : Expr) : M Bool := do
  return (← query (RegistrationGates.exactNodeHead (← projectType e))).isSort

def isProp (e : Expr) : M Bool := query (RegistrationGates.typedNodeProp e)
def isProof (e : Expr) : M Bool := do isProp (← projectType e)
def normalizeHead (e : Expr) : M Expr := query (RegistrationGates.exactNodeHead e)
def sameShape (a b : Expr) : M Bool := query (RegistrationGates.certifiedNodeRelation a b)

def withLocal (name : Name) (bi : BinderInfo) (type : Expr)
    (value : Option Expr) (body : Expr → M α) (nondep : Bool := false) : M α := do
  debit
  let locals := (← read).provenance.locals
  let mut index := locals.numIndices
  while locals.contains ⟨Name.num `compiledSourceLocal index⟩ do index := index + 1
  let id : FVarId := ⟨Name.num `compiledSourceLocal index⟩
  let locals := match value with
    | none => locals.mkLocalDecl id name type bi
    | some value => locals.mkLetDecl id name type value nondep
  withReader (fun context : Context => { context with provenance :=
    { context.provenance with locals } }) (body (mkFVar id))

private def withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr)
    (body : Expr → M α) : M α := withLocal name bi type none body

/-- Named record projections use only their compiled layout. The base and
explicit field arguments are existing checked terms. -/
def projectField (name : Name) (base : Expr) (arguments : Array Expr := #[]) : M Expr := do
  debit
  let some projection := (← read).provenance.view.getProjectionFnInfo? name
    | fail s!"incomplete_closure:E7.compiled_projection:{name}"
  let .ctorInfo ctor ← getConstInfo projection.ctorName
    | fail s!"incomplete_closure:E7.compiled_constructor:{projection.ctorName}"
  return mkAppN (← query (RegistrationGates.literalRecordField ctor.induct projection.i base)) arguments

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

partial def inContext (context : Array SourceBinder) (k : Array Expr → M α)
    (i : Nat := 0) (locals : Array Expr := #[]) : M α := do
  debit
  if i == context.size then return ← k locals
  let b := context[i]!
  let domain := b.domain.instantiateRev locals
  withLocal b.name b.info domain (b.value.map (·.instantiateRev locals)) (nondep := b.nondep) fun x =>
    inContext context k (i + 1) (locals.push x)

structure ReadoutScope where
  rawContext : Array SourceBinder
  rawObservation : Expr

structure DefinitionEntry where
  path : Array String
  owner : Name
  name : Name
  type : Expr
  value : Expr

structure Scope where
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

private partial def originalPath (node : Expr) : List String → Except String (List Contract.NodeEdge)
  | [] => pure []
  | edge :: rest => do
    let (selected, child) ← match edge, node with
      | "fn", .app f _ => pure (Contract.NodeEdge.function, f)
      | "arg", .app _ a => pure (Contract.NodeEdge.argument, a)
      | "domain", .lam _ t _ _ | "domain", .forallE _ t _ _ =>
        pure (Contract.NodeEdge.domain, t)
      | "body", .lam _ _ b _ | "body", .forallE _ _ b _ => pure (Contract.NodeEdge.body, b)
      | "type", .letE _ t _ _ _ => pure (Contract.NodeEdge.letType, t)
      | "value", .letE _ _ v _ _ => pure (Contract.NodeEdge.letValue, v)
      | "body", .letE _ _ _ b _ => pure (Contract.NodeEdge.letBody, b)
      | "body", .mdata _ b => pure (Contract.NodeEdge.metadata, b)
      | "body", .proj _ _ b => pure (Contract.NodeEdge.projection, b)
      | _, _ => throw "unclassified_form:source.coordinate_edge"
    return selected :: (← originalPath child rest)

private def observationAt (theoremName : Name) (definition : Option DefinitionEntry)
    (levels : List Name) (selected : SourceReadoutSelection) : M Contract.NodeCoordinate := do
  let (declaration, part, path) := match definition with
    | none => (theoremName, Contract.NodePart.type, selected.path)
    | some definition => (definition.name, Contract.NodePart.value,
        selected.path.extract definition.path.size selected.path.size)
  let owner ← ownerOf declaration
  let info ← getConstInfo declaration
  unless info.levelParams.length == levels.length do
    fail "contract.node_binding:source.coordinate_levels"
  let root ← match part with
    | .type => pure info.type
    | .value => match info.value? with
      | some value => pure value
      | none => fail "unclassified_form:source.coordinate_definition"
  let root := Contract.Literal.instantiateRawLevels info.levelParams
    (levels.map Level.param) root
  let path ← IO.ofExcept <| originalPath root path.toList
  return { owner, declaration, part, path, levels := levels.map Level.param }

private def boundObservationBody (theoremName : Name) (definition : Option DefinitionEntry)
    (levels : List Name) (selected : SourceReadoutSelection) (context : Array SourceBinder)
    (observation : Expr) : M Expr := do
  let location ← observationAt theoremName definition levels selected
  let closed := context.foldr (fun b e =>
    if let some value := b.value then Expr.letE b.name b.domain value e b.nondep
    else Expr.lam b.name b.domain e b.info) observation
  let some fact := (← read).provenance.nodeFacts.find? (fun fact =>
      fact.location == location && fact.relation == some (if selected.booleanPredicate then
        `LeanInformationAudit.Contract.BoolReflection else ``Contract.NodeFact.equal) &&
      fact.value.equal closed)
    | fail "unclassified_form:source.observation_fact_missing"
  let some observed := fact.other | fail "contract.node_binding:source.observation_endpoint"
  let mut body := observed
  for binder in context do
    debit
    body ← match binder.value, body with
      | none, .lam _ domain tail info =>
        unless binder.info == info && binder.domain.equal domain do
          fail "contract.node_binding:source.observation_telescope"
        pure tail
      | some value, .letE _ domain actualValue tail nondep =>
        unless binder.domain.equal domain && value.equal actualValue && binder.nondep == nondep do
          fail "contract.node_binding:source.observation_let"
        pure tail
      | _, _ => fail "contract.node_binding:source.observation_telescope"
  unless body.getAppFn.isConstOf `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout
      && body.getAppArgs.size == (if selected.functionOperand then 4 else 5) do
    fail "contract.node_binding:source.observation_readout"
  return body

/-- Literal parameter constructors preserve the selected data coordinates in
 order. Extra leaves must be original lexical proof or dictionary binders;
 they remain dependencies of the same full-telescope observation fact. -/
private partial def packedCoordinates (context : Array SourceBinder) (value : Expr)
    (expected : Array Expr) (position : Nat := 0) (retained : Array Nat := #[])
    (depth : Nat := 0) : M (Nat × Array Nat) := do
  debit
  if depth > 256 then fail "incomplete_closure:E8.source_parameter_depth"
  if expected[position]?.any (value.equal ·) then return (position + 1, retained)
  if let .bvar index := value then
    unless index < context.size do fail "contract.node_binding:source.parameter_scope"
    let ordinal := context.size - 1 - index
    let binder := context[ordinal]!
    unless binder.value.isNone do fail "contract.node_binding:source.parameter_let"
    let authorized ← inContext (context.extract 0 ordinal) fun locals => do
      let domain := binder.domain.instantiateRev locals
      return (← isProp domain) || (← dictionary domain)
    unless authorized do fail "contract.node_binding:source.parameter_unselected_data"
    return (position, if retained.contains ordinal then retained else retained.push ordinal)
  if let .mdata _ body := value then
    return ← packedCoordinates context body expected position retained (depth + 1)
  let .const constructorName _ := value.getAppFn
    | fail "contract.node_binding:source.parameter_literal"
  let .ctorInfo constructor ← getConstInfo constructorName
    | fail "contract.node_binding:source.parameter_constructor"
  let .inductInfo inductiveInfo ← getConstInfo constructor.induct
    | fail "contract.node_binding:source.parameter_inductive"
  unless inductiveInfo.ctors == [constructorName] &&
      value.getAppArgs.size == constructor.numParams + constructor.numFields do
    fail "contract.node_binding:source.parameter_layout"
  if constructor.numFields == 0 && !value.isConstOf ``PUnit.unit then
    fail "contract.node_binding:source.parameter_unselected_data"
  let mut next := position
  let mut captured := retained
  for field in value.getAppArgs.extract constructor.numParams value.getAppArgs.size do
    let (position, retained) ← packedCoordinates context field expected next captured (depth + 1)
    next := position
    captured := retained
  return (next, captured)

private def parameterSlots (context : Array SourceBinder) (value : Expr)
    (slots : Array Nat) : M (Array Nat) := do
  let expected := slots.map fun ordinal => Expr.bvar (context.size - 1 - ordinal)
  let (used, retained) ← packedCoordinates context value expected
  unless used == slots.size do fail "contract.node_binding:source.observation_parameters"
  return (slots ++ retained).toList.eraseDups.toArray.qsort (· < ·)

def resolve (info : ConstantInfo) (selection : SourceSelection) : M Scope := do
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
      unless definitionInfo.levelParams.length == info.levelParams.length do
        fail "unclassified_form:source.definition_universes"
      let reference := mkConst selected.name (info.levelParams.map Level.param)
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
      let value := Contract.Literal.instantiateRawLevels definitionInfo.levelParams
        (info.levelParams.map Level.param) declaration.value
      let type := Contract.Literal.instantiateRawLevels definitionInfo.levelParams
        (info.levelParams.map Level.param) definitionInfo.type
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
    coordinates := coordinates.push b
    previous := some i
  let readouts ← (selection.readouts.zip occurrences).mapM fun (selected, context, observation) => do
    let body ← boundObservationBody info.name definition info.levelParams selected context observation
    let actualSlots ← parameterSlots context body.getAppArgs[3]! slots
    for ordinal in actualSlots do
      discard <| transport (context.extract 0 ordinal)
        (actualSlots.filter (· < ordinal)) context[ordinal]!.domain
    if selected.functionOperand || selected.stateOperand.isSome then
      unless selected.stateBinder == 0 && !(selected.functionOperand && selected.stateOperand.isSome) &&
          !(selected.functionOperand && selected.booleanPredicate) do
        fail "unclassified_form:source.operand_mode"
      inContext context fun locals => do
        let term := observation.instantiateRev locals
        if selected.functionOperand then
          let .forallE _ domain output .default := (← projectType term)
            | fail "unclassified_form:source.function_operand"
          unless !output.hasLooseBVars && !(← isProp domain) && !(← isType term) &&
              !(← normalizeHead output).isSort do
            fail "unclassified_form:source.function_operand"
          discard <| transport context actualSlots observation
        else
          let path := selected.stateOperand.get!
          unless !path.isEmpty && path.size ≤ 256 do
            fail "unclassified_form:source.state_operand_path"
          let (inside, operand) ← atPath observation path
          unless inside.isEmpty do fail "unclassified_form:source.state_operand_scope"
          let operand := operand.instantiateRev locals
          unless !(← isProof operand) && !(← isType operand) do
            fail "unclassified_form:source.state_operand_data"
          if selected.booleanPredicate then
            unless ← isProp term do fail "unclassified_form:source.boolean_predicate"
          else
            unless !(← isProof term) && !(← isType term) do
              fail "unclassified_form:source.observation_data"
          let state ← projectType operand
          let extended := context.push { name := `state, info := .default, domain := state.abstract locals }
          let body ← replaceAt (observation.liftLooseBVars 0 1) path.toList (.bvar 0)
          discard <| transport extended (actualSlots.push context.size) body
      return { rawContext := context, rawObservation := observation : ReadoutScope }
    if selected.booleanPredicate then fail "unclassified_form:source.operand_mode"
    unless selected.stateBinder < context.size && actualSlots.all (· < selected.stateBinder) do
      fail "unclassified_form:source.state_binder"
    let stateBinder := context[selected.stateBinder]!
    if stateBinder.value.isSome then fail "unclassified_form:source.let_state"
    inContext context fun locals => do
      let term := observation.instantiateRev locals
      unless !(← isProof term) && !(← isType term) do
        fail "unclassified_form:source.observation_data"
      let output := (← projectType term).abstract locals
      discard <| transport context actualSlots output
    discard <| transport (context.extract 0 selected.stateBinder)
      (actualSlots.filter (· < selected.stateBinder)) stateBinder.domain
    discard <| transport context (actualSlots.push selected.stateBinder) observation
    return { rawContext := context, rawObservation := observation : ReadoutScope }
  return {
    definition := definition
    levels := info.levelParams
    selection := selection
    telescope := telescope
    coordinates := coordinates
    readouts := readouts }

private def family := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Completeness and duplicate freedom are kernel fields; the judge reads
 only the literal enumeration and its actual indexed carrier. -/
def enumeration (name : Name) (carrier : Expr) : M (Array Expr) := do
  let info ← getConstInfo name
  unless info.type.isAppOfArity `LeanInformationAudit.Contract.FiniteEnumeration 1 do
    fail "contract.node_binding:source.enumeration_type"
  unless ← sameShape info.type.appArg! carrier do
    fail "contract.node_binding:source.enumeration_carrier"
  let some value := info.value? | fail "contract.node_binding:source.enumeration_definition"
  let find := (← read).provenance.view.find?
  let fields ← IO.ofExcept <| Contract.Literal.fields find
    `LeanInformationAudit.Contract.FiniteEnumeration value 3
  let entries ← IO.ofExcept <| Contract.Literal.referencedValue find fields[0]!
  IO.ofExcept <| Contract.Literal.list "source.enumeration" entries

/-- A source observation is compared through its kernel-checked full-telescope
 Eq. The actual readout, role, parameter coordinates and state are literal
 operands of its right endpoint; no source expression is evaluated. -/
def validateFields (scope : Scope) (actual : Expr) (theoremName : Name)
    (roles : Array Expr) : M Unit := do
  unless roles.size == scope.readouts.size do fail "unclassified_form:source.roles"
  for h : i in [:scope.readouts.size] do
    debit
    let readout := scope.readouts[i]
    let selected := scope.selection.readouts[i]!
    let body ← boundObservationBody theoremName scope.definition scope.levels selected
      readout.rawContext readout.rawObservation
    let arguments := body.getAppArgs
    let expectedArity := if selected.functionOperand then 4 else 5
    unless arguments.size == expectedArity && arguments[1]!.equal actual &&
        arguments[2]!.equal roles[i]! do
      fail "contract.node_binding:source.observation_actual_role"
    discard <| parameterSlots readout.rawContext arguments[3]! scope.selection.coordinates
    unless selected.functionOperand do
      let state ← match selected.stateOperand with
        | none => pure (.bvar (readout.rawContext.size - 1 - selected.stateBinder))
        | some path => do
          let (inside, state) ← atPath readout.rawObservation path
          unless inside.isEmpty do fail "contract.node_binding:source.observation_state_scope"
          pure state
      unless arguments[4]!.equal state do fail "contract.node_binding:source.observation_state"

end LeanInformationAudit.CompiledSourceScope
