import LeanInformationAudit.Registry.Assessment
import LeanInformationAuditInterface.Store

namespace LeanInformationAudit.TemplateBinding
open Lean Meta TemplateAudit

/-- Scoped syntax input, never enrollment or certification authority. The
registration transaction owns rollback; the inner scope always clears itself. -/
private def eraseDescriptor (descriptor : Option Expr) (diagnostic : Option String) :
    Elab.Command.CommandElabM (Option Expr × Option String) := Elab.Command.liftTermElabM do
  try
    let descriptor ← descriptor.mapM fun value => do
      return (← TemplateAudit.withCumulativeBudget <| TemplateAudit.eraseProofs value
        (TemplateAudit.informationTemplate.work.get (← getOptions))).1
    return (descriptor, diagnostic)
  catch error =>
    return (none, some ("incomplete_closure:E8.descriptor_erasure:" ++
      (← error.toMessageData.toString)))

/-- Pure join validation grants no insertion or certification capability.
Both publication and authoritative assessment consume this same relation. -/
def joinClaims (events : Array (Name × TemplateOccurrenceEvent))
    (claims : Array (Name × TemplateBindingClaim)) :
    Except String (Array (TemplateOccurrenceEvent × Option TemplateBindingClaim)) := do
  let mut indexed : Std.HashMap TemplateOccurrenceKey TemplateOccurrenceEvent := {}
  for (producer, event) in events do
    unless producer == event.key.registrationModule do throw "incomplete_closure:dtr.event_owner"
    if indexed.contains event.key then throw "incomplete_closure:dtr.duplicate_occurrence"
    indexed := indexed.insert event.key event
  let mut selected : Std.HashMap TemplateOccurrenceKey TemplateBindingClaim := {}
  for (producer, claim) in claims do
    unless producer == claim.owner && claim.owner == claim.key.registrationModule do throw "incomplete_closure:dtr.claim_owner"
    unless indexed.contains claim.key do throw "unclassified_form:dtr.dangling_claim"
    if selected.contains claim.key then throw "unclassified_form:dtr.duplicate_claim"
    if let some event := indexed[claim.key]? then
      unless claim.arena.equal event.arena do throw "unclassified_form:dtr.claim_occurrence"
    selected := selected.insert claim.key claim
  return events.map fun (_, event) => (event, selected[event.key]?)

def sourcePath := TemplateAudit.sourcePath

def publishRegistration (rootId : Name) (entry : InformationRegistryEntry) : Elab.Command.CommandElabM Unit := do
  let info ← getConstInfo entry.theoremName
  let sourceRecord := (currentDeclaration (← getEnv)).bind (·.sourceRecord)
  let identity := if entry.sourceBound || sourceRecord.isSome then TemplateAudit.compactRawIdentity info.levelParams info.type
    else TemplateAudit.rawStatementIdentity info.levelParams info.type
  let statementIdentity := match identity with
    | .ok (identity, _) => identity
    | .error _ => ""
  let path := sourcePath entry.registrationModuleName
  let sourceIdentity ← try pure (Sha256.hex (← IO.FS.readBinFile (← Repository.source path))) catch _ => pure ""
  -- An occurrence can name a separate finite object arena. The original arena
  -- retains the source domain for witness and object-domain escape checks.
  let bridgeType := (← getConstInfo entry.realizationName).type
  let objectDomain ← Elab.Command.liftTermElabM do
    let arena ← mkConstWithFreshMVarLevels entry.arenaName
    let arenaType ← whnfR (← inferType arena)
    pure (arenaType.isConstOf RegistrationElaboration.objectDomainArenaName)
  let arenaName := if bridgeType.isAppOfArity RegistrationElaboration.witnessBridgeName 3 ||
      objectDomain then
      entry.arenaName else entry.canonicalObjectArenaName
  let event : TemplateOccurrenceEvent := {
    key := {
      root := entry.registrationModuleName
      registrationModule := entry.registrationModuleName
      theoremName := entry.theoremName
      objectArena := entry.canonicalObjectArenaName
      catalog := entry.effectiveCatalogId }

    unitName := entry.unitName, realizationName := sourceRecord.getD entry.realizationName,
    statement := info.type, levelParams := info.levelParams, statementIdentity,
    arena := mkConst arenaName,
    registrationSource := path, registrationSourceIdentity := sourceIdentity }
  let claim ← match currentDeclaration (← getEnv) with
    | none => pure none
    | some declaration =>
      let (descriptor, diagnostic) ← eraseDescriptor declaration.descriptor declaration.diagnostic
      let declaration := { declaration with descriptor, diagnostic }
      unless declaration.theoremName == event.key.theoremName && declaration.arena == event.key.objectArena do
        throwError "unclassified_form:dtr.inline_occurrence"
      pure <| some {
        key := event.key, arena := event.arena, descriptor := declaration.descriptor,
        resolutionDiagnostic := declaration.diagnostic, escapeInput := declaration.escapeInput, owner := rootId : TemplateBindingClaim }
  let record ← Elab.Command.liftTermElabM <| assess event claim
  modifyEnv fun current => addRecord (addOccurrence current event) record
  if let some claim := claim then modifyEnv (addClaim · claim)
  if record.result matches .undeclared then logWarning (missingDeclarationDiagnostic event.key)
  if let .declaredUnresolved diagnostic := record.result then logWarning diagnostic

/-- A replayed event cannot acquire current source or statement identities by
being exported from a new root. Check the original owner and retained bytes. -/
def validateEvent (event : TemplateOccurrenceEvent) : MetaM Unit := do
  let env ← getEnv
  unless event.registrationSource == sourcePath event.key.registrationModule &&
      event.key.root == event.key.registrationModule do
    throwError "incomplete_closure:dtr.event_owner"
  let input ← TemplateAudit.readSourceInput event.registrationSource
  unless input.sha256 == event.registrationSourceIdentity do
    throwError "incomplete_closure:dtr.event_source"
  let info ← getConstInfo event.key.theoremName
  let sourceBound := (← getConstInfo event.realizationName).type.isAppOfArity
    `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration 2
  let .ok (identity, _) := (if sourceBound then TemplateAudit.compactRawIdentity else
      TemplateAudit.rawStatementIdentity) info.levelParams info.type
    | throwError "incomplete_closure:dtr.event_statement"
  unless identity == event.statementIdentity && info.levelParams == event.levelParams &&
      info.type.equal event.statement do
    throwError "incomplete_closure:dtr.event_statement"
  unless env.contains event.unitName &&
      (RegistrationReifier.declaringModuleOf env event.unitName).getD env.header.mainModule ==
        event.key.registrationModule do
    throwError "incomplete_closure:dtr.event_unit_owner"
  let realizationOwner := (RegistrationReifier.declaringModuleOf env event.realizationName).getD
    env.header.mainModule
  unless env.contains event.realizationName &&
      moduleReachable env event.key.registrationModule realizationOwner do
    throwError "incomplete_closure:dtr.event_unit_owner"

/-- Snapshot for the complete imported join. Original producer records retain
the command inventory; selected contains one authoritative result per occurrence. -/
structure JoinedRecords where
  selected : Array BindingRecord
  originals : Array BindingRecord

/-- Join and assess the registrations of the modules in `reachable`, reading
the recorded occurrences of `env`. -/
private def joinRecords (env : Environment) (reachable : NameSet) (options : Options) :
    MetaM (Array BindingRecord) := withOptions (fun _ => options) do
  let selected (owner : Name) := reachable.contains owner
  let joined ← match joinClaims ((ownedEvents env).filter (selected ∘ Prod.fst))
      ((ownedClaims env).filter (selected ∘ Prod.fst)) with
    | .ok joined => pure joined
    | .error reason => throwError reason
  for (event, _) in joined do validateEvent event
  -- The imported registration universe grows with the repository. A retained
  -- assessment's currency check runs outside the template budget, so each
  -- occurrence owns a fresh fixed budget rather than sharing one for the join.
  joined.mapM fun (event, claim) => withCurrHeartbeats (assess event claim)

/-- Shared final assessment after the full imported claim set has been joined.
Callers must establish complete governed registration inputs before claiming coverage. -/
def assessJoined (input : RegistrationAssessmentInput) : MetaM (Array BindingRecord) := do
  unless sameRegistrationEnvironment input.environment (← getEnv) do
    throwError "incomplete_closure:dtr.assessment_environment"
  joinRecords input.environment (reachableModules input.environment input.rootId) input.options

private def snapshotRecords (env : Environment) (rootId : Name) (options : Options) :
    MetaM JoinedRecords := do
  let reachable := reachableModules env rootId
  let selected ← joinRecords env reachable options
  let originals ← ((inventory env).filter fun event =>
      reachable.contains event.key.registrationModule).mapM fun event => do
    let some original := (records (← getEnv)).find? (·.occurrence.key == event.key)
      | throwError "incomplete_closure:dtr.original_inventory"
    return original
  return { selected, originals }

/-- Join every registration reachable from the input root. The caller has
validated native coherence of the judge and of that root's closure. -/
def joinedSnapshot (input : RegistrationAssessmentInput) : MetaM JoinedRecords := do
  unless sameRegistrationEnvironment input.environment (← getEnv) do
    throwError "incomplete_closure:dtr.assessment_environment"
  snapshotRecords input.environment input.rootId input.options

/-- Export always starts by joining the entire loaded declaration universe. -/
def exportSnapshot (input : RegistrationAssessmentInput) : MetaM JoinedRecords := do
  -- Empty inventories still execute this judge. Validate its compiled source
  -- before collecting records.
  unless sameRegistrationEnvironment input.environment (← getEnv) do
    throwError "incomplete_closure:dtr.assessment_environment"
  TemplateAudit.NativeCoherence.validate #[`LeanInformationAudit.Registry]
  joinedSnapshot { input with environment := ← getEnv }

def keyJson (key : TemplateOccurrenceKey) : Json := Json.mkObj [
  ("root", toJson key.root.toString), ("registration_module", toJson key.registrationModule.toString),
  ("theorem", toJson key.theoremName.toString), ("object_arena", toJson key.objectArena.toString),
  ("catalog", toJson key.catalog.toString)]

private def certificateJson (certificate : TemplateBindingCertificate) : Json := Json.mkObj <| [
  ("key", keyJson certificate.key), ("evidence_ref", toJson certificate.evidenceRef),
  ("plan_identity", toJson certificate.planIdentity),
  ("descriptor_identity", toJson certificate.descriptorIdentity),
  ("actual_identity", toJson certificate.actualIdentity),
  ("argument_inputs", Json.arr (certificate.argumentInputs.map dependencyJson)),
  ("extraction_inputs", Json.arr (certificate.extractionInputs.map dependencyJson))] ++
  (certificate.sourceBinding.toList.map fun source => ("source_binding", source))

private def isRepositoryModule (name : Name) : Bool :=
  #[`D5, `Reg, `LeanInformationAudit, `LeanInformationAuditInterface].any (·.isPrefixOf name) ||
    name == `Trureturing

private def isRecordedModule (name : Name) : Bool :=
  #[`D5, `Reg, `LeanInformationAudit.Tests].any (·.isPrefixOf name) ||
    name == `Trureturing

private def moduleSourceInputs (env : Environment) (root : Name) :
    CoreM (Array TemplateAudit.SourceInput) := do
  let mut seen : NameSet := {}
  let mut pending := [root]
  let mut paths : Array String := #[]
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    unless isRepositoryModule name do continue
    if isRecordedModule name then
      let path := sourcePath name
      unless paths.contains path do paths := paths.push path
    let imports ← if name == env.header.mainModule then pure env.header.imports
      else if let some index := env.getModuleIdx? name then
        pure env.header.moduleData[index.toNat]!.imports
      else throwError "incomplete_closure:dtr.module_imports:{name}"
    pending := imports.toList.map (·.module) ++ pending
  TemplateAudit.readSourceInputs (paths.qsort (· < ·))

/-- Source inputs for census evidence and compile-time coherence fixtures.
Module report rows do not serialize these raw source hashes. -/
def moduleInputs (env : Environment) (root : Name) : CoreM (Array TemplateAudit.SourceInput) := do
  TemplateAudit.NativeCoherence.validate (#[root] ++
    (if root == env.header.mainModule then env.header.imports.map (·.module) else #[]))
  moduleSourceInputs env root

private def escapeFromJson (origin : EscapeFromIdentity) : Json := Json.mkObj [
  ("name", toJson origin.name.toString), ("type_identity", toJson origin.typeIdentity),
  ("object_identity", toJson origin.objectIdentity)]

private def escapeContinuationJson (residual : EscapeContinuationIdentity) : Json := Json.mkObj [
  ("kind", toJson residual.kind),
  ("declaration_name", toJson (residual.declarationName.map Name.toString)),
  ("statement_identity", toJson residual.statementIdentity),
  ("chain_name", toJson (residual.chainName.map Name.toString))]

/-- Shared record wire for the inspector and census authoritative snapshots. -/
def recordJson (record : BindingRecord) : MetaM Json := do
  let (state, diagnostic, certificate) := match record.result with
    | .undeclared => ("undeclared", toJson (missingDeclarationDiagnostic record.occurrence.key), Json.null)
    | .declaredUnresolved diagnostic => ("declared_unresolved", toJson diagnostic, Json.null)
    | .declaredValidated certificate => ("declared_validated", Json.null, certificateJson certificate)
  return Json.mkObj [
    ("key", keyJson record.occurrence.key),
    ("registration_source_path", toJson record.occurrence.registrationSource),
    ("statement_identity", toJson record.occurrence.statementIdentity),
    ("unit_name", toJson record.occurrence.unitName.toString),
    ("realization_name", toJson record.occurrence.realizationName.toString),
    ("escape_from", record.escape.fromObject.map escapeFromJson |>.getD Json.null),
    ("escape_continues", record.escape.continuation.map escapeContinuationJson |>.getD Json.null),
    ("bridge_kind", toJson record.escape.bridgeKind),
    ("binding_source_path", record.bindingOwner.map (toJson ∘ sourcePath) |>.getD Json.null),
    ("state", toJson state), ("diagnostic", diagnostic), ("certificate", certificate)]

/-- Each record is exported only by its registration owner. -/
private def moduleJson (snapshot : JoinedRecords) (moduleName : Name)
    (registered : Array TemplateOccurrenceKey) : MetaM Json := do
  let env ← getEnv
  let rows ← (snapshot.selected.filter
    (·.occurrence.key.registrationModule == moduleName)).mapM recordJson
  let version ← TemplateAudit.readReportCacheReleaseVersion
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("compatibility_version", toJson version),
    ("inventory", Json.arr ((inventory env).filter
      (·.key.registrationModule == moduleName) |>.map (keyJson ∘ TemplateOccurrenceEvent.key))),
    ("registered", Json.arr (registered.map keyJson)), ("records", Json.arr rows)]

/-- Native coherence roots of one report batch: the judge and every requested module. -/
def reportRoots (env : Environment) (modules : Array Name) : Array Name :=
  #[`LeanInformationAudit.Registry] ++ modules ++
    (if modules.contains env.header.mainModule then env.header.imports.map (·.module) else #[])

/-- One target's row, joined from the target's own semantic root. Registrations
of loaded modules the target does not import take no part in it. The caller
validates native coherence of the batch around all of its targets. -/
def targetJson (target : Name) (registered : Array TemplateOccurrenceKey) : MetaM Json := do
  moduleJson (← snapshotRecords (← getEnv) target (← getOptions)) target registered

/-- The row of a target that reaches no recorded input: the row `targetJson`
produces for it after its (empty) assessment. -/
def emptyTargetJson (target : Name) : MetaM Json :=
  moduleJson { selected := #[], originals := #[] } target #[]

/-- Validate the complete native union around a report transaction. Each native
snapshot is still checked against the loaded image; shared imports are rehashed
once per boundary, rather than once for every module that imports them. Neither
source hashes nor a caller-supplied validation flag can authorize this API. -/
def reportJson (modules : Array (Name × Array TemplateOccurrenceKey)) : MetaM (Array Json) := do
  let roots := reportRoots (← getEnv) (modules.map Prod.fst)
  TemplateAudit.NativeCoherence.validate roots
  let rows ← modules.mapM fun (moduleName, registered) => targetJson moduleName registered
  -- Compare the original snapshots after all records have been read. A replacement during this transaction cannot renew them.
  TemplateAudit.NativeCoherence.validate roots
  return rows

end LeanInformationAudit.TemplateBinding

namespace LeanInformationAudit
open Lean Meta


def registerValidatedEntry (rootId : Name) (entry : InformationRegistryEntry) :
    Lean.Elab.Command.CommandElabM Unit := do
  TemplateBinding.publishRegistration rootId (← registerSemanticEntry rootId entry)

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Meta

end LeanInformationAudit

namespace LeanInformationAudit
open Lean Meta Elab Command

private def distinctRecordedLevels : List Level → Bool
  | [] => true
  | level :: rest => !rest.contains level && distinctRecordedLevels rest

/-- Binding checks consume the expressions selected in the author's scope. -/
def validateRecordedBinding (input : RegistrationInput) : MetaM Unit := do
  let entry := input.entry
  if input.declaration.any (fun d => d.sourceRecord.isSome && !d.escapeInput.openContinuation) then
    throwError "unclassified_form:source.residual_requires_open"
  if entry.sourceBound then return
  let theoremInfo ← getConstInfo entry.theoremName
  let statement := theoremInfo.type
  let bridgeInfo ← getConstInfo entry.realizationName
  let checkedType := bridgeInfo.type.instantiateLevelParams bridgeInfo.levelParams
    (bridgeInfo.levelParams.map fun _ => .zero)
  unless ← withoutModifyingState <| RegistrationGates.checked entry.realizationName checkedType do
    throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
  let bridge ← mkConstWithFreshMVarLevels entry.realizationName
  let bridgeType ← whnfR (← inferType bridge)
  let args := bridgeType.getAppArgs
  if bridgeType.isAppOf `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization ||
      bridgeType.isAppOf TemplateAudit.escapeForwardBridge ||
      bridgeType.isAppOf RegistrationElaboration.witnessBridgeName then
    unless args.size == 3 && (← isDefEq args[1]! statement) do
      throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
    let arena ← mkConstWithFreshMVarLevels entry.arenaName
    let normalized ← RegistrationElaboration.normalizeArena arena
    let expectedArena := if normalized.witness then arena else normalized.law
    unless ← isDefEq args[0]! expectedArena do
      throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
    if bridgeType.isAppOf `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization then
      let levels := (← instantiateMVars arena).constLevels!
      unless levels.all (fun level => match level with
          | .param _ | .mvar _ => true | _ => false) && distinctRecordedLevels levels do
        throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
    if let some supplied := input.suppliedPrimitives then
      let expected ← compilePrimitiveBundle args[0]! args[2]!
      unless ← isDefEq supplied expected do
        throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
      checkWithKernel supplied
    if bridgeType.isAppOf RegistrationElaboration.witnessBridgeName then
      discard <| RegistrationGates.witnessStatement arena args[1]! entry.theoremName
      if let some diagnostic ← RegistrationGates.witnessEvidence arena args[2]!
          entry.variationWitness entry.sensitivityWitness then throwError diagnostic
    if bridgeType.isAppOf TemplateAudit.escapeForwardBridge &&
        (entry.variationWitness.isAnonymous || entry.sensitivityWitness.isAnonymous) then
      throwError "unclassified_form:dtr.forward_bridge_requires_sensitivity"

/-- A resolved enrollment is assessed by the same bounded compiler used by the report. -/
def assessRecordedEnrollment (owner : Name) (input : TemplateEnrollmentInput) :
    CommandElabM Unit := do
  unless input.version == 1 do
    logWarning m!"IE-C050 ClosedTruthReadout template={input.name} reason=unclassified_form rule=E4c.version"
    return
  match ← TemplateAudit.enroll owner input.options input.name input.constructors with
  | .ok () => pure ()
  | .error message =>
    logWarning m!"IE-C050 ClosedTruthReadout template={input.name} {TemplateAudit.diagnosticFields message}"

/-- No source syntax is re-elaborated. The recorder already chose all instances,
bridges and readouts; the judge reconstructs only its own proofs and assessments. -/
def assessRecordedEntry (owner : Name) (input : RegistrationInput) : CommandElabM Unit :=
    withScope (fun scope => { scope with opts := input.options }) do
  unless input.entry.registrationModuleName == owner && input.entry.derivedCertificate.isNone do
    throwError "incomplete_closure:dtr.input_owner"
  let entry ← liftTermElabM <| prepareRegistrationEntry owner (← getEnv) input.entry
  let entry := { entry with statementIdentity := theoremStatementIdentity (← getEnv) entry.theoremName }
  let entry ← match input.viaDescriptor with
    | none =>
      liftTermElabM <| validateRecordedBinding { input with entry }
      pure entry
    | some descriptor => liftTermElabM do
      for provider in #[RegistrationReifier.pointwiseProvider,
          RegistrationReifier.sensitivityProvider, RegistrationReifier.variationProvider] do
        discard <| RegistrationReifier.checkedProvider provider
      let arena ← RegistrationReifier.freezeArena entry.arenaName
      RegistrationReifier.derive entry arena descriptor input.outputEvidence
  match input.declaration with
  | none => registerValidatedEntry owner entry
  | some declaration =>
    let arena ← if entry.sourceBound || declaration.sourceRecord.isSome then
        pure declaration.arena
      else liftTermElabM <| resolveCanonicalArenaName declaration.arena
    unless declaration.theoremName == entry.theoremName && arena == entry.canonicalObjectArenaName do
      throwError "unclassified_form:dtr.inline_occurrence"
    TemplateBinding.withDeclaration { declaration with arena } do
      registerValidatedEntry owner entry


private def validateRecordedSource (owner : Name) (text : String) : CoreM Unit := do
  let current ← IO.FS.readFile (← Repository.source (TemplateAudit.sourcePath owner))
  unless current.crlfToLf == text.crlfToLf do throwError "incomplete_closure:dtr.input_source"

/-- Rebuild all judge state from the native raw-input containers. Both their
actual owners and their retained source bytes are checked before assessment. -/
def replayRegistrationInputs (input : RegistrationAssessmentInput) : CoreM Unit := do
  let saved ← getEnv
  tryCatchRuntimeEx (do
    let reachable := reachableModules saved input.rootId
    let selected (owner : Name) := reachable.contains owner
    let enrollments := (TemplateEnrollmentInputs.owned saved).filter (selected ∘ Prod.fst)
    let registrations := (RegistrationInputs.owned saved).filter (selected ∘ Prod.fst)
    let contracts := (RootCatalogs.owned saved).filter (selected ∘ Prod.fst)
    let mut roots : NameSet := {}
    for (owner, contract) in contracts do
      unless owner == contract.rootId do throwError "IE-C028 RootContractOwnerMismatch: {contract.rootId}"
      if roots.contains owner then throwError "IE-C028 DuplicateRootContract: {owner}"
      roots := roots.insert owner
    for (owner, expected) in ExpectedOccurrenceManifest.owned saved do
      if selected owner && owner != expected.rootId then
        throwError "incomplete_closure:dtr.expected_owner"
    for (owner, enrollment) in enrollments do
      unless owner == enrollment.owner do throwError "incomplete_closure:E7.import_owner"
      validateRecordedSource owner enrollment.sourceText
    for (owner, registration) in registrations do
      unless owner == registration.entry.registrationModuleName do
        throwError "incomplete_closure:dtr.input_owner"
      validateRecordedSource owner registration.sourceText
    modifyEnv fun env => TemplateAudit.resetTemplatePlans <|
      TemplateBinding.resetAssessmentRecords <| InformationRegistry.reset env
    liftCommandElabM do
      for (_, contract) in contracts do
        liftTermElabM <| RootCatalogs.acquireProvenance contract
      -- An independent expectation acquires its object arena's source evidence,
      -- rejecting live forwarding sources, before any registration is assessed.
      for (owner, expected) in ExpectedOccurrenceManifest.owned saved do
        if selected owner then
          discard <| liftTermElabM <| resolveCanonicalArenaName expected.objectArenaName
      for (owner, enrollment) in enrollments do assessRecordedEnrollment owner enrollment
      for (owner, registration) in registrations do
        GeneratedDeclarations.withOwner owner <| assessRecordedEntry owner registration
  ) fun error => do
    setEnv saved
    throw error

end LeanInformationAudit

run_cmd LeanInformationAudit.TemplateAudit.initializeGrammarPins
