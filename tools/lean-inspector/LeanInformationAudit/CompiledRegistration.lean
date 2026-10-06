import LeanInformationAudit.RegistrationRelations
import LeanInformationAudit.Contract.Decoder
import LeanInformationAudit.BindingWire
import LeanInformationAudit.ReadoutProvenance.State

namespace LeanInformationAudit.CompiledRegistration
open Lean TemplateAudit Contract

private def objectArena := `D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
private def lawArena := `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena
private def signature := `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature

def constant (find : Name → Option ConstantInfo) (name : Name) : IO ConstantInfo :=
  RawArtifacts.getConstant find name

/-- A companion is an immutable report view of an already compiled term.
No declaration is installed, compiled or checked. -/
def companion (find : Name → Option ConstantInfo) (context : RegistrationGates.QueryContext)
    (name : Name) (value : Expr) (isTheorem : Bool)
    (parameters : Option (List Name) := none) : IO ConstantInfo := do
  let type ← (RegistrationGates.typedNodeType value).run context
  unless Literal.closed value && Literal.closed type do
    throw <| IO.userError s!"incomplete_closure:contract.companion_open:{name}"
  let levels := parameters.getD
    (collectLevelParams (collectLevelParams {} type) value).params.toList
  if let some previous := find name then
    unless previous.levelParams == levels && previous.type.equal type &&
        previous.value? (allowOpaque := true) == some value do
      throw <| IO.userError s!"contract.companion_collision:{name}"
    return previous
  if isTheorem then
    return .thmInfo { name, levelParams := levels, type, value, all := [name] }
  else
    return .defnInfo {
      name, levelParams := levels, type, value, hints := .abbrev
      safety := .safe, all := [name] }

def prepare (find : Name → Option ConstantInfo) (owner : Name)
    (entry : InformationRegistryEntry) (resolvedArenaName : Name) : IO InformationRegistryEntry := do
  unless (find resolvedArenaName).isSome do
    throw <| IO.userError s!"IE-C003 ArenaResolutionFailed: {resolvedArenaName}"
  let info ← constant find entry.theoremName
  let statementIdentity := if info.isTheorem then "sha256:" ++ Sha256.hex (toString info.type).toUTF8 else ""
  return { entry with
    resolvedArenaName := resolvedArenaName, statementIdentity := statementIdentity
    registrationModuleName := if entry.registrationModuleName.isAnonymous then owner else entry.registrationModuleName }

/-- Typed obligations retain the compiler's mathematical checks; this checks
the bridge kind and named, closed witness claim required by the registry. -/
def validateBinding (find : Name → Option ConstantInfo) (input : RegistrationInput) : IO Unit := do
  let entry := input.entry
  if input.declaration.any (fun d => d.sourceRecord.isSome && !d.escapeInput.openContinuation) then
    throw <| IO.userError "unclassified_form:source.residual_requires_open"
  let some obligations := entry.compiledMathematics
    | throw <| IO.userError s!"contract.cannot_decode:{entry.theoremName}:missing_compiled_obligations"
  unless obligations.correspondence == .evidence do
    throw <| IO.userError s!"IE-C006 StatementProofMismatch: {entry.theoremName}"
  if let some source := input.realizationSource.filter (fun _ => !entry.sourceBound) then
    unless (← constant find source).isTheorem do
      throw <| IO.userError s!"IE-C006 StatementProofMismatch: {entry.theoremName}"

def validateCore (find : Name → Option ConstantInfo) (entry : InformationRegistryEntry) : IO Unit := do
  let some obligations := entry.compiledMathematics
    | throw <| IO.userError s!"contract.cannot_decode:{entry.theoremName}:missing_compiled_obligations"
  unless obligations.correspondence == .evidence do
    throw <| IO.userError s!"IE-C006 StatementProofMismatch: {entry.theoremName}"
  if entry.sourceBound then
    unless #[entry.theoremName, entry.unitName, entry.realizationName, entry.arenaName].all
        (fun name => (find name).isSome) do
      throw <| IO.userError "unclassified_form:source.registration_type"
    return
  if isCompanionName entry.theoremName then
    throw <| IO.userError s!"IE-C011 GeneratedCertificateRegistered: {entry.theoremName}"
  unless (find entry.theoremName).any (·.isTheorem) do
    throw <| IO.userError s!"IE-C001 UnregisteredTheoremUnit: {entry.theoremName}"
  for name in #[entry.unitName, entry.realizationName] do
    unless (find name).isSome do
      throw <| IO.userError s!"IE-C006 StatementProofMismatch: {entry.theoremName}"
  for name in #[entry.arenaName, entry.canonicalObjectArenaName] do
    unless (find name).isSome do
      throw <| IO.userError s!"IE-C003 ArenaResolutionFailed: {name}"
  unless (← constant find entry.unitName).type.getAppFn.isConstOf
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit do
    throw <| IO.userError s!"IE-C006 StatementProofMismatch: {entry.theoremName}"

def validateUnique (entry : InformationRegistryEntry) (entries : Array InformationRegistryEntry)
    (persisted : Bool := false) : IO Unit := do
  let occurrences := entries.filter (·.occurrenceKey == entry.occurrenceKey)
  if persisted then
    let [stored] := occurrences.toList
      | throw <| IO.userError (duplicateRegistrationError entry occurrences)
    unless sameEntry stored entry do
      throw <| IO.userError "P1.CertificateBindingMismatch: supplied entry differs from authoritative raw row"
  else unless occurrences.isEmpty do
    throw <| IO.userError (duplicateRegistrationError entry (occurrences.push entry))
  for (name, select) in #[(entry.unitName, InformationRegistryEntry.unitName),
      (entry.realizationName, InformationRegistryEntry.realizationName)] do
    let matching :=  entries.filter (fun candidate => select candidate == name)
    if persisted then
      unless matching.size == 1 && matching.all (sameEntry · entry) do
        throw <| IO.userError (qualifiedNameCollisionError entry.registrationModuleName
          entry.effectiveCatalogId name matching)
    else unless matching.isEmpty do
      throw <| IO.userError (qualifiedNameCollisionError entry.registrationModuleName
        entry.effectiveCatalogId name (matching.push entry))

private def variationError (entry : InformationRegistryEntry) (reason : String) : String :=
  s!"IE-C048 RealizationIgnoredByLaw key={entry.registrationModuleName}/{entry.effectiveCatalogId}/{entry.theoremName} law_arena={entry.arenaName} signature={entry.arenaName}.signature domain=all reason={reason}"

/-- Only finite index constructors are enumerated for partial support. The
mathematical variation and sensitivity obligations are read from their typed
constructors, preserving C048 precedence over C049. -/
def validateFinite (find : Name → Option ConstantInfo) (entry : InformationRegistryEntry)
    (options : Options) : IO (Option String) := do
  let some obligations := entry.compiledMathematics
    | throw <| IO.userError s!"contract.cannot_decode:{entry.theoremName}:missing_compiled_obligations"
  if obligations.variation != .evidence then
    return some <| variationError entry
      (if obligations.variation == .absent then "missing_witness" else "invalid_witness")
  if obligations.sensitivity == .evidence then return none
  let some readouts := obligations.partialReadouts
    | throw <| IO.userError s!"unclassified_form:finite.partial_readouts_missing:{entry.theoremName}"
  let some anchors := obligations.partialAnchors
    | throw <| IO.userError s!"unclassified_form:finite.partial_anchors_missing:{entry.theoremName}"
  let slots := (readouts.mapIdx fun i supported => (s!"readout[{i}]", supported)) ++
    (anchors.mapIdx fun i supported => (s!"anchor[{i}]", supported))
  let some failed := slots.find? (! ·.2) | return none
  let support := Json.arr (((slots.filter (·.2)).map (·.1)).qsort (· < ·) |>.map Json.str)
  return some s!"IE-C049 UnusedPrimitiveInBundle key={entry.registrationModuleName}/{entry.effectiveCatalogId}/{entry.theoremName} signature={entry.arenaName}.signature primitive={failed.1} support={support.compress}"

end LeanInformationAudit.CompiledRegistration
