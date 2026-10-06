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

private def expressionContext (options : Options) : M CompiledExpressions.Context := do
  let state ← get
  return CompiledRegistration.expressionContext (state.store.constants[·]?) (← IO.getNumHeartbeats) options

/-- Keep each alias's exact compiler term, inferred shape and target owner as
report data. This does not create or verify a mathematical declaration. -/
def keepCompanion (owner name : Name) (value : Expr) (isTheorem : Bool)
    (options : Options) (parameters : Option (List Name) := none) : M Unit := do
  let state ← get
  let info ← CompiledRegistration.companion (state.store.constants[·]?)
    (← expressionContext options) name value isTheorem parameters
  if state.generated.any (·.1 == name) then
    unless state.generated.contains (name, owner) do
      throw <| IO.userError s!"incomplete_closure:dtr.generated_owner:{name}"
    return
  modify fun state => { state with
    store := { state.store with
      constants := state.store.constants.insert name info
      owners := state.store.owners.insert name owner }
    generated := state.generated.push (name, owner) }

def prepareCompanions (owner : Name) (row : Decoder.CompanionInput) : M Unit := do
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
    let checked ← (CompiledEnrollment.compileTemplate owner input.name input.constructors).run
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

private unsafe def occurrence (owner : Name) (input : RegistrationInput) : M Unit := do
  let state ← get
  let entry := input.entry
  let info ← CompiledRegistration.constant (state.store.constants[·]?) entry.theoremName
  let sourceRecord := input.declaration.bind (·.sourceRecord)
  let identity := (if entry.sourceBound || sourceRecord.isSome then compactRawIdentity else rawStatementIdentity)
    info.levelParams info.type
  let statementIdentity := match identity with | .ok (identity, _) => identity | .error _ => ""
  let bridgeType := (← CompiledRegistration.constant (state.store.constants[·]?) entry.realizationName).type
  let arenaInfo ← CompiledRegistration.constant (state.store.constants[·]?) entry.arenaName
  let (arenaType, _) ← CompiledExpressions.run (← expressionContext input.options)
    (CompiledExpressions.head arenaInfo.type)
  let objectDomain := arenaType.isConstOf `D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
  let arenaName := if bridgeType.isAppOfArity
      `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization 3 ||
      objectDomain then entry.arenaName else entry.canonicalObjectArenaName
  let event : TemplateOccurrenceEvent := {
    key := {
      root := owner, registrationModule := owner, theoremName := entry.theoremName
      objectArena := entry.canonicalObjectArenaName, catalog := entry.effectiveCatalogId }
    unitName := entry.unitName, realizationName := sourceRecord.getD entry.realizationName
    statement := info.type, levelParams := info.levelParams, statementIdentity
    arena := mkConst arenaName
    registrationSource := TemplateBinding.sourcePath owner
    registrationSourceIdentity := ""
    compiledMathematics := entry.compiledMathematics }
  let claim ← input.declaration.mapM fun declaration => do
    let arena ← if entry.sourceBound || declaration.sourceRecord.isSome then pure declaration.arena else
      IO.ofExcept <| resolveCanonicalArenaName (state.store.constants[·]?) declaration.arena
    unless declaration.theoremName == entry.theoremName && arena == entry.canonicalObjectArenaName do
      throw <| IO.userError "unclassified_form:dtr.inline_occurrence"
    let (descriptor, diagnostic) ← try
      let context := (← enrollmentContext owner input.options).provenance
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
  prepareCompanions owner row
  let entry ← CompiledRegistration.prepare ((← get).store.constants[·]?) owner input.entry
  CompiledRegistration.validateBinding ((← get).store.constants[·]?) { input with entry }
  CompiledRegistration.validateCore ((← get).store.constants[·]?) entry
  CompiledRegistration.validateUnique entry (entriesFor (← get) owner)
  let diagnostic ← if entry.sourceBound then pure none else
    CompiledRegistration.validateFinite ((← get).store.constants[·]?) entry input.options
  let type := (← CompiledRegistration.constant ((← get).store.constants[·]?) entry.realizationName).type
  if type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization &&
      diagnostic.isSome then
    throw <| IO.userError s!"unclassified_form:dtr.forward_bridge_requires_sensitivity:{diagnostic.get!}"
  if type.isAppOfArity
      `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization 3 then
    if let some diagnostic := diagnostic then throw <| IO.userError diagnostic
  keepDiagnostic entry diagnostic
  modify fun state => { state with entries := state.entries.push entry }
  occurrence owner { input with entry }

/-- Every reachable occurrence and claim passes the complete join relation and
the current compiled assessor. Targets in the same batch never contribute. -/
unsafe def assessJoined (root : Name) (options : Options := {}) : M (Array BindingRecord) := do
  let state ← get
  let reachable := reachableModules (importsOf state.store) root
  let joined ← IO.ofExcept <| TemplateBinding.joinClaims
    (state.events.filter (fun row => reachable.contains row.1))
    (state.claims.filter (fun row => reachable.contains row.1))
  joined.mapM fun (event, claim) => do
    (CompiledAssessment.assess event claim).run {
      enrollment := ← enrollmentContext root options, plans := state.plans }

unsafe def prepareSnapshot (snapshot : Discovery.Snapshot) : M Unit := do
  for (_, catalog) in snapshot.roots do
    for row in catalog.expected ++ catalog.source ++ catalog.baseline do
      discard <| IO.ofExcept <| resolveCanonicalArenaName ((← get).store.constants[·]?) row.objectArenaName
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
