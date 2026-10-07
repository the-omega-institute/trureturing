import LeanInformationAudit.CompiledRegistration
import LeanInformationAudit.Contract.Discovery

namespace LeanInformationAudit.ArtifactRegistration
open Lean TemplateAudit Contract

/-- Target-local report data. Companion views never enter a Lean environment. -/
structure State where
  store : RawArtifacts.Store
  entries : Array InformationRegistryEntry := #[]
  events : Array (Name × TemplateOccurrenceEvent) := #[]
  claims : Array (Name × TemplateBindingClaim) := #[]
  plans : TemplateIndex := {}
  generated : Array (Name × Name) := #[]
  records : Array BindingRecord := #[]
  enrollmentErrors : Array String := #[]
  coverageInputs : Array (TemplateOccurrenceKey × Array Contract.NodeFacts.BoundOperand) := #[]
  activeFacts : Array Contract.NodeFacts.BoundOperand := #[]

abbrev M := StateT State IO

def importsOf (store : RawArtifacts.Store) (name : Name) : Array Name :=
  (store.modules.find? name).map (·.imports.map (·.module)) |>.getD #[]

def entriesFor (state : State) (root : Name) : Array InformationRegistryEntry :=
  let reachable := reachableModules (importsOf state.store) root
  state.entries.filter (fun entry => reachable.contains entry.registrationModuleName)

private unsafe def enrollmentContext (owner : Name) (options : Options) : M CompiledEnrollment.Context := do
  let state ← get
  let names := state.entries.foldl (fun names entry => names.insert entry.theoremName) ({} : NameSet)
  CompiledEnrollment.Context.fromArtifacts state.store owner options names

private unsafe def expressionContext (owner : Name) (options : Options) : M RegistrationGates.QueryContext := do
  let context := (← enrollmentContext owner options).provenance
  return { context with nodeFacts := (← get).activeFacts }

/-- Source leaves come from the actual target and selected D5 definition,
independently of certificate claims. Their types and D5 data dependencies stay
in the inventory; source proofs do not contribute implementation bodies. -/
private def sourceLeaves (view : Contract.NodeFacts.View) (target : Name)
    (roots : Array Contract.NodeCoordinate) : Except String NameSet := do
  let some targetInfo := view.find target
    | throw s!"incomplete_closure:E7.compiled_constant:{target}"
  let mut pending := targetInfo.type.getUsedConstants.toList
  for root in roots do
    if root.part == .value && (`D5).isPrefixOf root.owner then
      pending := (← Contract.NodeFacts.locate view root).getUsedConstants.toList ++ pending
  let mut found : NameSet := {}
  let mut remaining := 524288
  while let name :: rest := pending do
    pending := rest
    if found.contains name then continue
    unless remaining > 0 do throw "incomplete_closure:E8.source_inventory"
    remaining := remaining - 1
    found := found.insert name
    let some info := view.find name
      | throw s!"incomplete_closure:E7.compiled_constant:{name}"
    let some owner := view.owner name
      | throw s!"incomplete_closure:E7.compiled_owner:{name}"
    pending := info.type.getUsedConstants.toList ++ pending
    if (`D5).isPrefixOf owner && !info.isTheorem then
      if let some value := info.value? then
        pending := value.getUsedConstants.toList ++ pending
  return found

/-- Keep each alias's exact compiler term, inferred shape and target owner as
report data. This does not create or verify a mathematical declaration. -/
unsafe def keepCompanion (owner name : Name) (value : Expr) (isTheorem : Bool)
    (options : Options) (parameters : Option (List Name) := none) : M Unit := do
  let state ← get
  let info ← CompiledRegistration.companion (state.store.constants[·]?)
    (← expressionContext owner options) name value isTheorem parameters
  if state.generated.any (·.1 == name) then
    unless state.generated.contains (name, owner) do
      throw <| IO.userError s!"incomplete_closure:dtr.generated_owner:{name}"
    return
  modify fun state => { state with
    store := { state.store with
      constants := state.store.constants.insert name info
      owners := state.store.owners.insert name owner }
    generated := state.generated.push (name, owner) }

unsafe def prepareCompanions (owner : Name) (row : Decoder.CompanionInput) : M Unit := do
  let entry := row.input.entry
  let options := row.input.options
  if entry.sourceBound then
    let record ← CompiledRegistration.constant ((← get).store.constants[·]?) entry.realizationName
    keepCompanion owner entry.unitName
      (mkConst entry.realizationName (record.levelParams.map Level.param)) false options
      (some record.levelParams)
    return
  if row.generated || row.bridge.constName? != some entry.realizationName then
    keepCompanion owner entry.realizationName row.bridge true options
  let some unit := row.unit | throw <| IO.userError "contract.registration:unit_missing"
  keepCompanion owner entry.unitName unit false options

private def keepDiagnostic (entry : InformationRegistryEntry) (diagnostic : Option String) : M Unit := do
  let name := (entry.unitName.str entry.registrationModuleName.toString).str
    "__information_registration_diagnostic"
  let info : ConstantInfo := .defnInfo {
    name, levelParams := [], type := mkConst ``String, value := mkStrLit (diagnostic.getD ""),
    hints := .abbrev, safety := .safe, all := [name] }
  if let some previous := (← get).store.constants[name]? then
    unless previous.type.equal info.type && previous.value? == info.value? &&
        (← get).generated.contains (name, entry.registrationModuleName) do
      throw <| IO.userError s!"registration diagnostic binding mismatch:{name}"
  modify fun state => { state with
    store := { state.store with
      constants := state.store.constants.insert name info
      owners := state.store.owners.insert name entry.registrationModuleName }
    generated := if state.generated.contains (name, entry.registrationModuleName) then state.generated
      else state.generated.push (name, entry.registrationModuleName) }

unsafe def enroll (owner : Name) (input : TemplateEnrollmentInput) : M Unit := do
  let result ← try
    unless input.version == 1 do throw <| IO.userError "unclassified_form:E4c.version"
    let checked ← (CompiledEnrollment.compileTemplate owner input.enrollmentName input.name input.constructors input.bodyFact input.coverage).run
      (← enrollmentContext owner input.options)
    let current := (← get).plans
    match ← current.lookup input.name (pure () : IO Unit) with
    | .ok _ => throw <| IO.userError "unclassified_form:E7.duplicate_enrollment"
    | .error _ => pure ()
    if let some reason := current.error then throw <| IO.userError reason
    if current.bytes + checked.retainedBytes > 8388608 then
      throw <| IO.userError "incomplete_closure:E8.import_bytes"
    modify fun state => { state with plans := current.insertChecked checked }
    pure none
  catch error => pure (some error.toString)
  if let some reason := result then
    modify fun state => { state with
      enrollmentErrors := state.enrollmentErrors.push s!"IE-C050 ClosedTruthReadout template={input.name} {reason}" }

private unsafe def occurrence (owner : Name) (input : RegistrationInput) (target arena : Expr) : M Unit := do
  let state ← get
  let entry := input.entry
  let info ← CompiledRegistration.constant (state.store.constants[·]?) entry.theoremName
  unless target.isConstOf info.name && target.constLevels!.length == info.levelParams.length do
    throw <| IO.userError "contract.node_binding:registration.target_levels"
  let levelParams ← target.constLevels!.mapM fun level =>
    match level with
    | .param name => pure name
    | _ => throw <| IO.userError "contract.node_binding:registration.target_rigid_levels"
  let statement := Contract.Literal.instantiateRawLevels info.levelParams target.constLevels! info.type
  let sourceRecord := input.declaration.bind (·.sourceRecord)
  let identity := (if entry.sourceBound || sourceRecord.isSome then compactRawIdentity else rawStatementIdentity)
    levelParams statement
  let statementIdentity := match identity with | .ok (identity, _) => identity | .error _ => ""
  let event : TemplateOccurrenceEvent := {
    key := {
      root := owner, registrationModule := owner, theoremName := entry.theoremName
      objectArena := entry.canonicalObjectArenaName, catalog := entry.effectiveCatalogId }
    unitName := entry.unitName, realizationName := sourceRecord.getD entry.realizationName
    statement, levelParams, statementIdentity
    arena
    registrationSource := TemplateBinding.sourcePath owner
    registrationSourceIdentity := ""
    compiledMathematics := entry.compiledMathematics }
  let claim ← input.declaration.mapM fun declaration => do
    let suppliedArena := if entry.objectArenaName.isAnonymous then entry.arenaName else entry.objectArenaName
    unless declaration.theoremName == entry.theoremName && declaration.arena == suppliedArena do
      throw <| IO.userError "unclassified_form:dtr.inline_occurrence"
    let (descriptor, diagnostic) ← try
      let context ← expressionContext owner input.options
      let descriptor ← declaration.descriptor.mapM fun expression => do
        return (← (CompiledEvidence.eraseProofs expression (informationTemplate.work.get input.options)).run context).1
      pure (descriptor, declaration.diagnostic)
    catch error => pure (none, some s!"incomplete_closure:E8.descriptor_erasure:{error}")
    return {
      key := event.key, arena := event.arena, descriptor,
      resolutionDiagnostic := diagnostic, escapeInput := declaration.escapeInput, owner : TemplateBindingClaim }
  -- Owner, statement and companions come directly from this target's compiled
  -- snapshot, rather than from replayed extension events or caller certificates.
  unless (state.store.owners[entry.unitName]?) == some owner &&
      moduleReachable (importsOf state.store) owner
        ((state.store.owners[event.realizationName]?).getD .anonymous) do
    throw <| IO.userError "incomplete_closure:dtr.event_unit_owner"
  modify fun state => { state with
    events := state.events.push (owner, event)
    claims := match claim with | none => state.claims | some claim => state.claims.push (owner, claim) }

unsafe def register (owner : Name) (row : Decoder.CompanionInput) : M Unit := do
  let input := row.input
  unless input.entry.registrationModuleName == owner && input.entry.derivedCertificate.isNone &&
      input.viaDescriptor.isNone do
    throw <| IO.userError "incomplete_closure:dtr.input_owner"
  let context ← enrollmentContext owner input.options
  let initialView : Contract.NodeFacts.View := {
    find := context.provenance.view.find?
    owner := context.provenance.view.ownerOf
    external := fun n => context.extern n || context.implementedBy n }
  let leaves ← IO.ofExcept <| sourceLeaves initialView input.entry.theoremName input.coverageRoots
  let view := { initialView with
    sourceLeaf := fun name =>
      leaves.contains name || !RegistrationGates.inProtected context.provenance.view name }
  let coverageDiagnostic := match Contract.NodeFacts.coverage view input.coverageRoots input.coverage with
    | .ok _ => none
    | .error reason =>
      if reason.startsWith "contract.node_binding:closure_unsafe:" ||
          reason.startsWith "contract.node_binding:unsafe:" ||
          reason.startsWith "contract.node_binding:fact_safety:" then
        some s!"forbidden_dependency:E6.registration_coverage:{reason}"
      else if reason == "contract.node_binding:coverage_fuel" then
        some s!"incomplete_closure:E8.registration_coverage:{reason}"
      else some s!"incomplete_closure:E7.registration_coverage:{reason}"
  let fs ← IO.ofExcept <| Contract.Literal.fields view.find ``Contract.NodeCoverage input.coverage 2
  let factTable ← IO.ofExcept <| Contract.Literal.resolveReferences view.find fs[1]!
  let names ← IO.ofExcept <| Contract.Literal.list "registration.facts" factTable
  let facts ← names.mapM fun e => do
    let name ← IO.ofExcept <| Contract.Literal.name "registration.fact" e
    let axioms ← context.collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throw <| IO.userError s!"forbidden_dependency:registration.fact_axioms:{name}"
    IO.ofExcept <| Contract.NodeFacts.fact view name
  modify fun state => { state with activeFacts := facts.flatten }
  let arenaRootIndex := if input.entry.objectArenaName.isAnonymous then 2 else 3
  let some arenaRoot := input.coverageRoots[arenaRootIndex]?
    | throw <| IO.userError "contract.node_binding:arena.root_missing"
  let arenaRef ← IO.ofExcept <| Contract.Literal.referencedValue view.find
    (← IO.ofExcept <| Contract.NodeFacts.locate view arenaRoot)
  let (_, rawArena) ← IO.ofExcept <| Contract.Literal.reference view.find "arena" arenaRef.getAppArgs.back!
  let canonicalArena ← IO.ofExcept <| resolveCanonicalArena view.find facts.flatten rawArena
  prepareCompanions owner row
  let entry ← CompiledRegistration.prepare ((← get).store.constants[·]?) owner input.entry
    canonicalArena.getAppFn.constName!
  CompiledRegistration.validateBinding ((← get).store.constants[·]?) { input with entry }
  CompiledRegistration.validateCore ((← get).store.constants[·]?) entry
  CompiledRegistration.validateUnique entry (entriesFor (← get) owner)
  let finiteDiagnostic ← if entry.sourceBound then pure none else
    CompiledRegistration.validateFinite ((← get).store.constants[·]?) entry input.options
  let type := (← CompiledRegistration.constant ((← get).store.constants[·]?) entry.realizationName).type
  if type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization &&
      finiteDiagnostic.isSome then
    throw <| IO.userError s!"unclassified_form:dtr.forward_bridge_requires_sensitivity:{finiteDiagnostic.get!}"
  let diagnostic := coverageDiagnostic.or finiteDiagnostic
  keepDiagnostic entry diagnostic
  modify fun state => { state with entries := state.entries.push entry }
  let declaration := input.declaration.map fun declaration => {
    declaration with diagnostic := coverageDiagnostic.or declaration.diagnostic }
  occurrence owner { input with entry, declaration } row.target canonicalArena
  let state ← get
  let some (_, event) := state.events.back? | throw <| IO.userError "incomplete_closure:registration.event"
  modify fun state => { state with coverageInputs := state.coverageInputs.push (event.key, state.activeFacts) }

/-- Every reachable occurrence and claim passes the complete join relation and
the current compiled assessor. Targets in the same batch never contribute. -/
unsafe def assessJoined (root : Name) (options : Options := {}) : M (Array BindingRecord) := do
  let state ← get
  let reachable := reachableModules (importsOf state.store) root
  let joined ← IO.ofExcept <| TemplateBinding.joinClaims
    (state.events.filter (fun row => reachable.contains row.1))
    (state.claims.filter (fun row => reachable.contains row.1))
  joined.mapM fun (event, claim) => do
    let context ← enrollmentContext root options
    let some (_, facts) := state.coverageInputs.find? (fun row => row.1 == event.key)
      | throw <| IO.userError "incomplete_closure:registration.coverage_input"
    (CompiledAssessment.assess event claim).run {
      enrollment := { context with provenance := { context.provenance with nodeFacts := facts } }, plans := state.plans }

unsafe def prepareSnapshot (snapshot : Discovery.Snapshot) : M Unit := do
  for (_, catalog) in snapshot.roots do
    for row in catalog.expected ++ catalog.source ++ catalog.baseline do
      unless ((← get).store.constants[row.objectArenaName]?).isSome do
        throw <| IO.userError s!"IE-C003 ArenaResolutionFailed: {row.objectArenaName}"
  for (owner, enrollment) in snapshot.enrollments do enroll owner enrollment
  for (owner, registration) in snapshot.registrations do register owner registration

def targetJson (target : Name) (state : State) : IO Json := do
  let own := state.events.filter (·.1 == target) |>.map Prod.snd
  let rows ← (state.records.filter (·.occurrence.key.registrationModule == target)).mapM TemplateBinding.recordJson
  let registered := (state.entries.filter (·.registrationModuleName == target)).map fun entry => {
    root := target, registrationModule := target, theoremName := entry.theoremName
    objectArena := entry.canonicalObjectArenaName, catalog := entry.effectiveCatalogId : TemplateOccurrenceKey }
  return Json.mkObj [ ("schema_version", toJson (1 : Nat)),
    ("inventory", Json.arr (own.map (TemplateBinding.keyJson ∘ TemplateOccurrenceEvent.key))),
    ("registered", Json.arr (registered.map TemplateBinding.keyJson)), ("records", Json.arr rows)]

end LeanInformationAudit.ArtifactRegistration
