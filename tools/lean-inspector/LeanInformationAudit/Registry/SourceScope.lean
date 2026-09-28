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

/-- Expand only lexical let references, from their original raw values. The target
scope stays fixed while a value is interpreted in its strictly earlier context.
`extraDepth` lifts free coordinates under the occurrence's internal binders;
new binders inside the value keep their own de Bruijn indices. No definitions,
proofs or dictionaries become independently variable parameters. -/
partial def expandLets (context : Array SourceBinder) (scope : Nat) (e : Expr)
    (localDepth : Nat := 0) (extraDepth : Nat := 0) (depth : Nat := 0) : M Expr := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.source_depth"
  let child := fun x => expandLets context scope x localDepth extraDepth (depth + 1)
  let bound := fun x => expandLets context scope x (localDepth + 1) extraDepth (depth + 1)
  match e with
  | .bvar i =>
    if i < localDepth then return e
    let i := i - localDepth
    unless i < context.size do throwError "unclassified_form:source.open_coordinate"
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
  | .mvar _ | .fvar _ => throwError "unclassified_form:source.open_expression"
  | _ => return e

/-- Capture-avoiding projection with a raw inverse check after source-determined
local-let transport. Apply to domains and outputs as well as observations. -/
def transport (context : Array SourceBinder) (slots : Array Nat) (e : Expr) : M Expr := do
  let expanded ← expandLets context context.size e
  let projected ← project slots context.size expanded
  unless (← project slots context.size projected true).equal expanded do
    throwError "unclassified_form:source.inverse_mapping"
  return projected

def atPath (source : Expr) (path : Array String) : M (Array SourceBinder × Expr) := do
  if path.size > 256 then throwError "incomplete_closure:E8.source_path"
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
      | _, _ => throwError "unclassified_form:source.absent_occurrence"
  return (context, e)

/-- Replace one explicit raw occurrence, without entering definitions or binders. -/
partial def replaceAt (e : Expr) (path : List String) (value : Expr) : M Expr := do
  debit
  match path, e with
  | [], _ => return value
  | "fn" :: rest, .app f a => return .app (← replaceAt f rest value) a
  | "arg" :: rest, .app f a => return .app f (← replaceAt a rest value)
  | _, _ => throwError "unclassified_form:source.state_operand_path"

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
  rawContext : Array SourceBinder := #[]
  rawObservation : Expr := default

private structure PreparedReadout where
  context : Array SourceBinder
  observation : Expr
  state : Expr
  output : Expr
  rawContext : Array SourceBinder
  rawObservation : Expr

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
  /-- Original lexical indices selected as parameters.  `coordinates` remains
      the user-selected semantic data projection; `support` contains only
      omitted class-valued instance binders needed by that projection. -/
  parameterSlots : Array Nat
  coordinates : Array SourceBinder
  /-- Raw source binders used to authenticate omitted instance support. -/
  supportRaw : Array SourceBinder
  support : Array SourceBinder
  parameters : Array SourceBinder
  readouts : Array ReadoutScope

private partial def dictionary (type : Expr) : MetaM Bool := do
  let type ← withTransparency .all <| whnf type
  forallTelescope type fun _ result => do
    pure (Lean.isClass (← getEnv) (result.getAppFn.constName?.getD .anonymous))

private partial def referencedPaths (context : Array SourceBinder) (e : Expr)
    (localDepth : Nat := 0) (depth : Nat := 0) : M (Array (Array String)) := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.source_support_depth"
  let child := fun x => referencedPaths context x localDepth (depth + 1)
  let bound := fun x => referencedPaths context x (localDepth + 1) (depth + 1)
  let join := fun (left right : Array (Array String)) =>
    left.foldl (init := right) fun acc path => if acc.contains path then acc else acc.push path
  match e with
  | .bvar i =>
    if i < localDepth then return #[]
    let i := i - localDepth
    unless i < context.size do throwError "unclassified_form:source.open_coordinate"
    return #[context[context.size - 1 - i]!.path]
  | .app f a => return join (← child f) (← child a)
  | .lam _ t b _ | .forallE _ t b _ => return join (← child t) (← bound b)
  | .letE _ t v b _ =>
    return join (join (← child t) (← child v)) (← bound b)
  | .mdata _ b | .proj _ _ b => return ← child b
  | .mvar _ | .fvar _ => throwError "unclassified_form:source.open_expression"
  | _ => return #[]

private def supportCandidate (context : Array SourceBinder) (index : Nat) : M Bool := do
  let b := context[index]!
  if b.info != .instImplicit || b.value.isSome then return false
  inContext (context.extract 0 index) (fun locals => do
    let domain := b.domain.instantiateRev locals
    if domain == mkSort .zero || (← isProp domain) then return false
    return ← dictionary domain)

private def addSupportClosure (coordinateContext : Array SourceBinder)
    (coordinateSlots : Array Nat) (roots : Array (Array (Array String))) : M (Array Nat) := do
  let coordinatePaths := coordinateSlots.map (fun i => coordinateContext[i]!.path)
  let mut pending := roots.flatten
  let mut paths : Array (Array String) := #[]
  while !pending.isEmpty do
    debit
    let path := pending[0]!
    pending := pending.extract 1 pending.size
    if coordinatePaths.contains path || paths.contains path then continue
    let some index := coordinateContext.findIdx? (fun b => b.path == path)
      | throwError "unclassified_form:source.captured_support"
    let binder := coordinateContext[index]!
    if let some value := binder.value then
      -- A lexical let is source syntax, not a parameter.  Expand its raw
      -- value in the strictly earlier context before deciding whether any
      -- actual instance support is needed.
      let dependencies ← referencedPaths (coordinateContext.extract 0 index) value
      pending := pending ++ dependencies
      continue
    unless ← supportCandidate coordinateContext index do
      throwError "unclassified_form:source.coordinate_dependency"
    paths := paths.push path
    let earlier := coordinateContext.extract 0 index
    let dependencies ← referencedPaths earlier (← expandLets earlier earlier.size binder.domain)
    pending := pending ++ dependencies
  return paths.map fun path => coordinateContext.findIdx? (fun b => b.path == path) |>.get!

private def prepareReadout (selected : SourceReadoutSelection)
    (context : Array SourceBinder) (observation : Expr) : M PreparedReadout := do
  if selected.functionOperand || selected.stateOperand.isSome then
    unless selected.stateBinder == 0 &&
        !(selected.functionOperand && selected.stateOperand.isSome) &&
        !(selected.functionOperand && selected.booleanPredicate) do
      throwError "unclassified_form:source.operand_mode"
    let (state, body) ← inContext context fun locals => do
      let term := observation.instantiateRev locals
      if selected.functionOperand then
        let .forallE _ domain output .default := (← inferType term)
          | throwError "unclassified_form:source.function_operand"
        unless !output.hasLooseBVars && domain != mkSort .zero &&
            !(← isProp domain) && !(← dictionary domain) && !(← isType term) do
          throwError "unclassified_form:source.function_operand"
        let typeArgument ← withLocalDeclD `state domain fun state => isType state
        if typeArgument then throwError "unclassified_form:source.function_operand"
        return (domain.abstract locals, mkApp (observation.liftLooseBVars 0 1) (.bvar 0))
      let path := selected.stateOperand.get!
      unless !path.isEmpty && path.size ≤ 256 do
        throwError "unclassified_form:source.state_operand_path"
      let pair ← atPath observation path
      let inside := pair.1
      let operand := pair.2
      unless inside.isEmpty do throwError "unclassified_form:source.state_operand_scope"
      let operand := operand.instantiateRev locals
      unless !(← isProof operand) && !(← isType operand) do
        throwError "unclassified_form:source.state_operand_data"
      let state ← inferType operand
      if (← dictionary state) then throwError "unclassified_form:source.state_operand_data"
      let body ← replaceAt (observation.liftLooseBVars 0 1) path.toList (.bvar 0)
      return (state.abstract locals, body)
    let extended := context.push {name := `state, info := .default, domain := state}
    let body ← if selected.booleanPredicate then
        inContext extended fun locals => do
          let term := body.instantiateRev locals
          unless ← isProp term do throwError "unclassified_form:source.boolean_predicate"
          return (← mkDecide term).abstract locals
      else pure body
    let output ← inContext extended fun locals => do
      let term := body.instantiateRev locals
      unless !(← isProof term) && !(← isType term) do
        throwError "unclassified_form:source.observation_data"
      let output ← inferType term
      if (← dictionary output) then throwError "unclassified_form:source.observation_data"
      return output.abstract locals
    return PreparedReadout.mk extended body state output context observation
  if selected.booleanPredicate then throwError "unclassified_form:source.operand_mode"
  unless selected.stateBinder < context.size do
    throwError "unclassified_form:source.state_binder"
  let stateBinder := context[selected.stateBinder]!
  if stateBinder.value.isSome then throwError "unclassified_form:source.let_state"
  inContext (context.extract 0 selected.stateBinder) fun locals => do
    let domain := stateBinder.domain.instantiateRev locals
    if stateBinder.info == .instImplicit || domain == mkSort .zero ||
        (← isProp domain) || (← dictionary domain) then
      throwError "unclassified_form:source.dictionary_or_proof_state"
  let output ← inContext context fun locals => do
    let term := observation.instantiateRev locals
    unless !(← isProof term) && !(← isType term) do
      throwError "unclassified_form:source.observation_data"
    let output ← inferType term
    if (← dictionary output) then throwError "unclassified_form:source.observation_data"
    return output.abstract locals
  return PreparedReadout.mk context observation stateBinder.domain output context observation

def resolve (info : ConstantInfo) (selection : SourceSelection) : M Scope := do
  unless info.isTheorem do throwError "unclassified_form:source.theorem"
  let owner := (RegistrationReifier.declaringModuleOf (← getEnv) info.name).getD
    (← getEnv).header.mainModule
  unless selection.owner == owner do throwError "unclassified_form:source.owner"
  let definition : Option DefinitionEntry ← match selection.definition with
    | none => pure none
    | some selected => do
      unless selected.owner == owner do throwError "unclassified_form:source.definition_owner"
      let definitionInfo ← getConstInfo selected.name
      let definitionOwner := (RegistrationReifier.declaringModuleOf (← getEnv) selected.name).getD
        (← getEnv).header.mainModule
      unless definitionOwner == owner do
        throwError "unclassified_form:source.definition_owner"
      let .defnInfo declaration := definitionInfo
        | throwError "unclassified_form:source.definition_kind"
      debit
      if definitionInfo.isUnsafe ||
          (Compiler.getImplementedBy? (← getEnv) selected.name).isSome ||
          (getExternAttrData? (← getEnv) selected.name).isSome then
        throwError "forbidden_dependency:source.definition_safety"
      unless definitionInfo.type == mkSort .zero do
        throwError "unclassified_form:source.definition_type"
      unless definitionInfo.levelParams.length == info.levelParams.length do
        throwError "unclassified_form:source.definition_universes"
      let reference := mkConst selected.name (info.levelParams.map Level.param)
      let occurrence ← if selected.path.isEmpty then pure info.type
        else if selected.path == #["arg"] && info.type.isAppOfArity ``Not 1 then
          pure info.type.getAppArgs[0]!
        else throwError "unclassified_form:source.definition_path"
      unless occurrence.equal reference do
        throwError "unclassified_form:source.definition_reference"
      for readout in selection.readouts do
        unless selected.path.size < readout.path.size &&
            readout.path.extract 0 selected.path.size == selected.path do
          throwError "unclassified_form:source.definition_readout_path"
      let value := declaration.value.instantiateLevelParams definitionInfo.levelParams
        (info.levelParams.map Level.param)
      let type := definitionInfo.type.instantiateLevelParams definitionInfo.levelParams
        (info.levelParams.map Level.param)
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
    if telescope.size ≥ 64 then throwError "incomplete_closure:E8.source_binders"
    telescope := telescope.push { name := n, info := bi, domain := d : SourceBinder }
    e := b
  let slots := selection.coordinates
  if slots.size > 64 || selection.readouts.isEmpty || selection.readouts.size > 64 then
    throwError "unclassified_form:source.selection_size"
  if (selection.readouts.map (·.path)).toList.eraseDups.length != selection.readouts.size then
    throwError "unclassified_form:source.duplicate_occurrence"
  let occurrences ← selection.readouts.mapM fun selected => atPath source selected.path
  let coordinateContext := occurrences[0]!.1
  let mut previous : Option Nat := none
  let mut coordinates := #[]
  for i in slots do
    debit
    unless i < coordinateContext.size && previous.all (· < i) do
      throwError "unclassified_form:source.coordinate_order"
    let b := coordinateContext[i]!
    -- Exact source ancestry, never equality of names or binder domains alone.
    for (context, _) in occurrences do
      debit (b.path.size + 1)
      unless context[i]?.any (fun other => other.path == b.path) do
        throwError "unclassified_form:source.captured_coordinate"
    inContext (coordinateContext.extract 0 i) fun locals => do
      let domain := b.domain.instantiateRev locals
      if b.info == .instImplicit || domain == mkSort .zero ||
          (← isProp domain) || (← dictionary domain) then
        throwError "unclassified_form:source.dictionary_or_proof_coordinate"
    if b.value.isSome then throwError "unclassified_form:source.let_coordinate"
    coordinates := coordinates.push b
    previous := some i
  -- Prepare every selected readout before collecting support.  This keeps
  -- state abstraction occurrence-specific and makes state/output type
  -- dependencies part of the same closure as coordinate domains.
  let prepared ← (selection.readouts.zip occurrences).mapM fun (selected, (context, observation)) =>
    prepareReadout selected context observation
  let mut roots : Array (Array (Array String)) := #[]
  for i in slots do
    let earlier := coordinateContext.extract 0 i
    roots := roots.push (← referencedPaths earlier (← expandLets earlier earlier.size coordinateContext[i]!.domain))
  for ((selected, _), prepared) in (selection.readouts.zip occurrences).zip prepared do
    let varyingPath := if selected.functionOperand || selected.stateOperand.isSome then
        prepared.context[prepared.context.size - 1]!.path
      else prepared.context[selected.stateBinder]!.path
    let bodyRefs ← referencedPaths prepared.context
      (← expandLets prepared.context prepared.context.size prepared.observation)
    roots := roots.push (bodyRefs.filter (· != varyingPath))
    let stateContext := if selected.functionOperand || selected.stateOperand.isSome then prepared.rawContext
      else prepared.rawContext.extract 0 selected.stateBinder
    let stateRefs ← referencedPaths stateContext
      (← expandLets stateContext stateContext.size prepared.state)
    roots := roots.push (stateRefs.filter (· != varyingPath))
    let outputRefs ← referencedPaths prepared.context
      (← expandLets prepared.context prepared.context.size prepared.output)
    roots := roots.push (outputRefs.filter (· != varyingPath))
  let supportSlots := (← addSupportClosure coordinateContext slots roots).qsort (· < ·)
  if slots.size + supportSlots.size > 64 then
    throwError "incomplete_closure:E8.source_binders"
  for index in supportSlots do
    let path := coordinateContext[index]!.path
    for (context, _) in occurrences do
      unless context[index]?.any (fun binder => binder.path == path) do
        throwError "unclassified_form:source.captured_support"
  let parameterSlots := (slots ++ supportSlots).qsort (· < ·)
  let mut parameters := #[]
  for i in parameterSlots do
    let b := coordinateContext[i]!
    let domain ← transport (coordinateContext.extract 0 i) (parameterSlots.filter (· < i)) b.domain
    parameters := parameters.push { b with domain }
  let support := parameters.filter fun b => supportSlots.any fun i =>
    coordinateContext[i]!.path == b.path
  let supportRaw := supportSlots.map (fun i => coordinateContext[i]!)
  let readouts ← prepared.mapIdxM fun i prepared => do
    let selected := selection.readouts[i]!
    let context := prepared.rawContext
    let observation := prepared.rawObservation
    if selected.functionOperand || selected.stateOperand.isSome then
      let state ← transport context parameterSlots prepared.state
      let output ← transport prepared.context parameterSlots prepared.output
      let projected ← transport prepared.context (parameterSlots.push context.size) prepared.observation
      return {
        context := prepared.context
        observation := prepared.observation
        state, output, projected
        rawContext := context
        rawObservation := observation : ReadoutScope }
    unless selected.stateBinder < context.size && parameterSlots.all (· < selected.stateBinder) do
      throwError "unclassified_form:source.state_binder"
    let output ← transport context parameterSlots prepared.output
    let state ← transport (context.extract 0 selected.stateBinder) parameterSlots prepared.state
    let projected ← transport context (parameterSlots.push selected.stateBinder) observation
    return ReadoutScope.mk context observation state output projected context observation
  let mut reconstructedSource := source
  for (selected, context, observation) in selection.readouts.zip occurrences do
    if selected.booleanPredicate then
      let reified ← inContext context fun locals => do
        let term := observation.instantiateRev locals
        unless ← isProp term do throwError "unclassified_form:source.boolean_predicate"
        return (← mkEq (← mkDecide term) (mkConst ``Bool.true)).abstract locals
      reconstructedSource ← replaceAt reconstructedSource selected.path.toList reified
  return {
    source := info.type
    expanded := reconstructedSource
    definition := definition
    levels := info.levelParams
    selection := selection
    telescope := telescope
    parameterSlots := parameterSlots
    coordinates := coordinates
    supportRaw := supportRaw
    support := support
    parameters := parameters
    readouts := readouts }

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

/-- Compare the original support at its source-derived syntax positions. Source
heads are opaque during administrative exposure of the actual field: unfolding
a dictionary-ignoring source function would destroy precisely this evidence.
Unrelated subterms remain the responsibility of the ordinary kernel comparison.
In particular, an occurrence in a discarded argument or another field cannot
stand in for the dictionary operand at this position. -/
private partial def capture (support : Array Expr) (source actual : Expr)
    (depth : Nat := 0) : M Unit := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.source_capture_depth"
  if !(source.find? (support.contains ·)).isSome then return
  if source.equal actual then return
  let heads := source.getUsedConstants
  let actual ← withCanUnfoldPred (fun _ info => pure (!heads.contains info.name)) <|
    whnf actual
  if source.getAppFn.isConst then
    unless source.getAppFn == actual.getAppFn do
      throwError "unclassified_form:source.actual_support_link"
  let next := fun a b => capture support a b (depth + 1)
  match source, actual with
  | .fvar a, .fvar b =>
    unless a == b do throwError "unclassified_form:source.actual_support_link"
  | .app f a, .app g b => next f g; next a b
  | .lam n t b bi, .lam _ u c _ | .forallE n t b bi, .forallE _ u c _ =>
    next t u
    fun fuel => withLocalDecl n bi t fun x =>
      (next (b.instantiate1 x) (c.instantiate1 x)).run fuel
  | .mdata _ b, _ => next b actual
  | .letE _ _ v b _, _ => next (b.instantiate1 v) actual
  | .proj n i b, .proj m j c =>
    unless n == m && i == j do throwError "unclassified_form:source.actual_support_link"
    next b c
  | _, _ => throwError "unclassified_form:source.actual_support_link"

/-- Enter the packed telescope with the same rigid locals on both sides. This
also checks dictionary uses in later dependent parameter domains. -/
private partial def captureParameters (scope : Scope) (source actual : Expr)
    (index : Nat := 0) (support : Array Expr := #[]) : M Unit := do
  debit
  if scope.support.isEmpty || index ≥ scope.parameters.size then return
  if index + 1 == scope.parameters.size then
    capture support source actual
    return
  let actual ← withCanUnfoldPred (fun _ info => pure (info.name != ``Sigma)) <| whnf actual
  unless source.isAppOfArity ``Sigma 2 && actual.isAppOfArity ``Sigma 2 do
    throwError "unclassified_form:source.params"
  let left := source.getAppArgs
  let right := actual.getAppArgs
  capture support left[0]! right[0]!
  let binder := scope.parameters[index]!
  fun fuel => withLocalDecl binder.name binder.info left[0]! fun x => do
    let support := if scope.support.any (fun b => b.path == binder.path) then support.push x else support
    (captureParameters scope (mkApp left[1]! x).headBeta (mkApp right[1]! x).headBeta
      (index + 1) support).run fuel

/-- Every selected role is checked at the actual source occurrence and its type.
Coordinate projection is inverted before this kernel equality is used. -/
def validateFields (scope : Scope) (signature actual : Expr) : M Unit := do
  let params ← packedType scope.parameters 0 #[]
  unless ← isDefEq params (← mkAppM (family ++ `Signature.Params) #[signature]) do
    throwError "unclassified_form:source.params"
  captureParameters scope params (← mkAppM (family ++ `Signature.Params) #[signature])
  let roles ← RegistrationGates.indices
    (← mkAppM (family ++ `Signature.Role) #[signature])
    (← mkAppM (family ++ `Signature.finiteRole) #[signature])
  unless roles.size == scope.readouts.size do throwError "unclassified_form:source.roles"
  inContext scope.parameters fun locals => do
    let parameter ← packedValue params locals 0
    let support := (scope.parameters.zip locals).filterMap fun (binder, value) =>
      if scope.support.any (fun b => b.path == binder.path) then some value else none
    for (role, readout) in roles.zip scope.readouts do
      debit
      let state := readout.state.instantiateRev locals
      let output := readout.output.instantiateRev locals
      checkWithKernel state
      checkWithKernel output
      capture support state (← mkAppM (family ++ `Signature.State) #[signature, parameter])
      capture support output (← mkAppM (family ++ `Signature.Output) #[signature, role, parameter])
      unless (← isType state) && (← isType output) &&
          (← isDefEq state (← mkAppM (family ++ `Signature.State) #[signature, parameter])) &&
          (← isDefEq output (← mkAppM (family ++ `Signature.Output) #[signature, role, parameter])) do
        throwError "unclassified_form:source.state_or_output"
      let observation := Expr.lam `state readout.state readout.projected .default
      let observation := observation.instantiateRev locals
      let actualReadout ← mkAppM (family ++ `Realization.readout) #[actual, role, parameter]
      capture support observation actualReadout
      unless ← isDefEq observation actualReadout do
        throwError "unclassified_form:source.actual_observation"

/-- Definitional reconstruction checks every hypothesis, dictionary and conclusion.
BinderInfo is checked explicitly since Lean defeq alone ignores it. -/
partial def reconstruct (source law : Expr) (depth : Nat := 0) : M Unit := do
  debit
  if depth > 256 then throwError "incomplete_closure:E8.reconstruction_depth"
  let law ← withConfig (fun c => { c with zeta := false }) <| whnf law
  -- `whnf` exposes Not as an implication. Keep its source polarity and inspect
  -- the full proposition underneath, including binder modes ignored by defeq.
  if source.isAppOfArity ``Not 1 then
    let .forallE _ domain body .default := law
      | throwError "unclassified_form:source.statement_reconstruction"
    unless body.equal (mkConst ``False) do
      throwError "unclassified_form:source.statement_reconstruction"
    reconstruct source.getAppArgs[0]! domain (depth + 1)
    return
  match source, law with
  | .letE n d v b _, .letE _ d' v' b' _ =>
    reconstruct d d' (depth + 1)
    unless ← isDefEq v v' do throwError "unclassified_form:source.let_reconstruction"
    fun fuel => withLetDecl n d v fun x =>
      (reconstruct (b.instantiate1 x) (b'.instantiate1 x) (depth + 1)).run fuel
  | .letE .., _ => throwError "unclassified_form:source.missing_let"
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
