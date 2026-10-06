import LeanInformationAudit.Registry.Reifier
import LeanInformationAudit.RuntimeInputs
import LeanInformationAudit.CompiledRegistration
import LeanInformationAudit.Registry.ArenaProvenance

namespace LeanInformationAudit

open Lean
open Lean.Meta

private def theoremUnitName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

private def primitiveLawArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena

private def primitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization

private def legacyPrimitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization

def InformationRegistryEntry.lawArenaName (entry : InformationRegistryEntry) : Name :=
  entry.arenaName

namespace RootCatalogs

/-- Acquire all independent inputs while compiling a contract. A source or baseline
row need not be registered or expected. Keep the supplied identities and membership
unchanged; only the compiler's provenance extension receives evidence. -/
def acquireProvenance (contract : RootCatalogContract) : MetaM Unit := do
  for row in contract.expected ++ contract.source ++ contract.baseline do
    discard <| ofExcept <| resolveCanonicalArenaName ((← getEnv).find? ·) row.objectArenaName

end RootCatalogs

/-- Keep occurrence order for consumers and index theorem membership for the
per-node identity guard. Both views belong to the same environment state, so
imports, insertion and transaction rollback cannot leave the index stale.
Only entries are persisted; the index is reconstructed on import. -/
structure InformationRegistryState where
  entries : Array InformationRegistryEntry := #[]
  theoremNames : NameSet := {}
  deriving Inhabited

private initialize informationRegistryExt : EnvExtension InformationRegistryState ←
  registerEnvExtension (pure {})

def InformationRegistry.reset (env : Environment) : Environment :=
  informationRegistryExt.setState env {}

def InformationRegistry.entries (env : Environment) :
    Array InformationRegistryEntry :=
  (informationRegistryExt.getState env).entries

def InformationRegistry.find? (env : Environment) (theoremName : Name) :
    Option InformationRegistryEntry :=
  (entries env).find? fun entry => entry.theoremName == theoremName

def InformationRegistry.hasTheorem (env : Environment) (n : Name) : Bool :=
  (informationRegistryExt.getState env).theoremNames.contains n

def InformationRegistry.hasOccurrence (env : Environment)
    (objectArena theoremName : Name) : Bool :=
  (entries env).any fun entry =>
    entry.canonicalObjectArenaName == objectArena && entry.theoremName == theoremName

def InformationRegistry.hasUnit (env : Environment) (n : Name) : Bool :=
  (entries env).any fun entry => entry.unitName == n

/-- Reflect direct module imports; graph queries consume only these names. -/
def moduleImports (env : Environment) (name : Name) : Array Name :=
  let imports := if name == env.header.mainModule then env.header.imports else
    match env.getModuleIdx? name with
    | some index => env.header.moduleData[index.toNat]!.imports
    | none => #[]
  imports.map (·.module)

def InformationRegistry.forRoot (env : Environment) (root : Name) :
    Array InformationRegistryEntry :=
  let reachable := reachableModules (moduleImports env) root
  entries env |>.filter (fun entry => reachable.contains entry.registrationModuleName)

/-- A deterministic identity for the theorem type stored in the elaborated environment. -/
def theoremStatementIdentity (env : Environment) (theoremName : Name) : String :=
  match env.find? theoremName with
  | some (.thmInfo info) => "sha256:" ++ Sha256.hex (toString info.type).toUTF8
  | _ => ""

/-- Resolve the independent expectation source for one sealing root. -/
def expectedOccurrencesForRoot (env : Environment) (rootId : Name) :
    Array ExpectedOccurrence :=
  let rows := match RootCatalogs.find? env rootId with
    | some contract => snapshotExpectations rootId contract.expected
    | none => #[]
  rows.map fun row =>
    let identity := if !row.statementIdentity.isEmpty then row.statementIdentity
      else row.capturedStatement.map
        (fun type => "sha256:" ++ Sha256.hex (toString type).toUTF8) |>.getD ""
    { row with statementIdentity := identity }


/-- Resolve the prospective owner before any admission precheck. -/
def prepareRegistrationEntry (rootId : Name) (env : Environment)
    (entry : InformationRegistryEntry) : MetaM InformationRegistryEntry := do
  let spelling := if entry.objectArenaName.isAnonymous then entry.arenaName
    else entry.objectArenaName
  let resolvedArenaName ← ofExcept <| resolveCanonicalArenaName (env.find? ·) spelling
  return { entry with
    resolvedArenaName
    registrationModuleName := if entry.registrationModuleName.isAnonymous then
      rootId else entry.registrationModuleName }


private def statementMismatchError (name : Name) : String :=
  s!"IE-C006 StatementProofMismatch: {name}"

/-- The report checks the supplied bridge, including before a generated alias. -/
def isTheoremBridge (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.thmInfo _) => true
  | _ => false

/-- Perform the environment-only checks shared by admission and sealing. -/
private def validateEntryDeclarations (env : Environment)
    (entry : InformationRegistryEntry) :
    Except String Unit := do
  if isCompanionName entry.theoremName then
    throw s!"IE-C011 GeneratedCertificateRegistered: {entry.theoremName}"
  match env.find? entry.theoremName with
  | some (.thmInfo _) => pure ()
  | _ => throw s!"IE-C001 UnregisteredTheoremUnit: {entry.theoremName}"
  unless env.contains entry.unitName do
    throw (statementMismatchError entry.theoremName)
  unless env.contains entry.arenaName do
    throw s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
  unless env.contains entry.canonicalObjectArenaName do
    throw s!"IE-C003 ArenaResolutionFailed: {entry.canonicalObjectArenaName}"
  unless env.contains entry.realizationName do
    throw (statementMismatchError entry.theoremName)
  let unitInfo := env.find? entry.unitName |>.get!
  unless unitInfo.type.getAppFn.constName? == some theoremUnitName do
    throw (statementMismatchError entry.theoremName)

def compilePrimitiveBundle (arenaExpr realizationExpr : Expr) : MetaM Expr := do
  let arenaExpr := (← RegistrationElaboration.normalizeArena arenaExpr).law
  let realizationType <- instantiateMVars (← whnfR (← inferType realizationExpr))
  unless realizationType.getAppFn.constName? == some primitiveRealizationName do
    throwError "realization type mismatch"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "realization argument mismatch"
  let expectedSignature <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.signature
    #[arenaExpr]
  unless ← isDefEq realizationArgs[1]! expectedSignature do
    throwError "realization signature mismatch"
  let arenaValue <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
    #[arenaExpr]
  let stateType <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.State #[arenaValue]
  let stateDecidableEq <- mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.Arena.stateDecidableEq #[arenaValue]
  let compiler <- mkConstWithFreshMVarLevels
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle
  return mkAppN compiler
    #[stateType, realizationArgs[1]!, stateDecidableEq, realizationExpr]

/-- Complete the declaration and definitional-equality checks shared by both phases. -/
private def validateEntryCore (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  if entry.compiledMathematics.isSome then
    let result : IO (Except String Unit) := do
      try
        CompiledRegistration.validateCore (env.find? ·) entry
        return .ok ()
      catch error => return .error error.toString
    return ← result
  if entry.sourceBound then
    try
      let source ← getConstInfo entry.theoremName
      let unit ← getConstInfo entry.unitName
      let record ← getConstInfo entry.realizationName
      unless source.isTheorem && unit.type.equal record.type && record.type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration 2 &&
          record.levelParams.length == source.levelParams.length do
        return .error "unclassified_form:source.registration_type"
      unless env.contains entry.arenaName && entry.objectArenaName == entry.arenaName &&
          entry.resolvedArenaName == entry.arenaName do
        return .error "unclassified_form:source.arena_identity"
      return .ok ()
    catch _ => return .error "unclassified_form:source.registration_type"
  match validateEntryDeclarations env entry with
  | .error message => return .error message
  | .ok () => pure ()
  try
    if entry.derivedCertificate.isSome then
      let spelling := if entry.objectArenaName.isAnonymous then entry.arenaName
        else entry.objectArenaName
      unless entry.statementIdentity == theoremStatementIdentity env entry.theoremName &&
          entry.resolvedArenaName == (← ofExcept <| resolveCanonicalArenaName (env.find? ·) spelling) do
        return .error "P1.CertificateBindingMismatch: current statement identity or arena ownership"
    RegistrationReifier.validateDerivedCertificate entry
  catch e => return .error (← e.toMessageData.toString)
  tryCatchRuntimeEx (do
    let theoremExpr <- mkConstWithFreshMVarLevels entry.theoremName
    let theoremType <- instantiateMVars (← whnfR (← inferType theoremExpr))
    let unitExpr <- mkConstWithFreshMVarLevels entry.unitName
    let unitType <- instantiateMVars (← whnfR (← inferType unitExpr))
    unless unitType.getAppFn.constName? == some theoremUnitName do
      return .error (statementMismatchError entry.theoremName)
    let unitArgs := unitType.getAppArgs
    if unitArgs.isEmpty then
      return .error (statementMismatchError entry.theoremName)
    let arenaExpr <- mkConstWithFreshMVarLevels entry.arenaName
    let normalized ← RegistrationElaboration.normalizeArena arenaExpr
    let expectedArena := normalized.finite
    let objectArenaExpr <- if entry.objectArenaName.isAnonymous then
      pure expectedArena
    else
      let objectArenaExpr <- mkConstWithFreshMVarLevels entry.objectArenaName
      let objectArenaType <- instantiateMVars (← whnfR (← inferType objectArenaExpr))
      unless objectArenaType.getAppFn.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.Arena do
        return .error s!"IE-C003 ArenaResolutionFailed: {entry.objectArenaName}"
      unless ← isDefEq expectedArena objectArenaExpr do
        return .error (statementMismatchError entry.theoremName)
      pure objectArenaExpr
    unless ← isDefEq unitArgs.back! objectArenaExpr do
      return .error (statementMismatchError entry.theoremName)
    let statementExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.Statement
      #[unitExpr]
    let statementType <- instantiateMVars (← whnfR statementExpr)
    let proofExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.proof
      #[unitExpr]
    let proofType <- instantiateMVars (← whnfR (← inferType proofExpr))
    unless ← isDefEq statementType theoremType do
      return .error (statementMismatchError entry.theoremName)
    unless ← isDefEq proofType statementType do
      return .error (statementMismatchError entry.theoremName)
    let realizationExpr <- mkConstWithFreshMVarLevels entry.realizationName
    let realizationType <- instantiateMVars (← whnfR (← inferType realizationExpr))
    let realizationHead := realizationType.getAppFn.constName?
    if realizationHead == some primitiveRealizationName then
      let expectedLaw <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.Law
        #[normalized.law, realizationExpr]
      unless ← isDefEq theoremType expectedLaw do
        return .error (statementMismatchError entry.theoremName)
      let primitivesExpr <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
        #[unitExpr]
      let compiledBundle <- compilePrimitiveBundle arenaExpr realizationExpr
      unless ← isDefEq primitivesExpr compiledBundle do
        return .error (statementMismatchError entry.theoremName)
    else if realizationHead == some legacyPrimitiveRealizationName ||
        realizationHead == some `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization ||
        realizationHead == some RegistrationElaboration.witnessBridgeName then
      if isTheoremBridge env entry.realizationName then
        let legacyArgs := realizationType.getAppArgs
        unless legacyArgs.size == 3 do
          return .error (statementMismatchError entry.theoremName)
        let expectedBridgeArena := if realizationHead == some RegistrationElaboration.witnessBridgeName then
          arenaExpr else normalized.law
        unless ← isDefEq legacyArgs[0]! expectedBridgeArena do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[1]! theoremType do
          return .error (statementMismatchError entry.theoremName)
        if realizationHead == some RegistrationElaboration.witnessBridgeName then
          discard <| RegistrationGates.witnessStatement arenaExpr legacyArgs[1]! entry.theoremName
        let primitivesExpr <- mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
          #[unitExpr]
        let compiledBundle <- compilePrimitiveBundle arenaExpr legacyArgs[2]!
        unless ← isDefEq primitivesExpr compiledBundle do
          return .error (statementMismatchError entry.theoremName)
      else return .error (statementMismatchError entry.theoremName)
    else
      return .error (statementMismatchError entry.theoremName)
    return .ok ()) fun e => do
    if entry.derivedCertificate.isSome && e.isRuntime then
      return .error s!"P1.IncompleteCheck: {← e.toMessageData.toString}"
    return .error (statementMismatchError entry.theoremName)

/-- Validate a prospective entry before insertion; neither registry key may exist yet. -/
def validateNewEntry (rootId : Name) (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  let entries := InformationRegistry.forRoot env rootId
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  if !occurrenceMatches.isEmpty then
    return .error (duplicateRegistrationError entry (occurrenceMatches.push entry))
  let unitMatches := entries.filter fun candidate =>
    candidate.unitName == entry.unitName
  if !unitMatches.isEmpty then
    return .error <| qualifiedNameCollisionError entry.registrationModuleName
      entry.effectiveCatalogId entry.unitName (unitMatches.push entry)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  if !realizationMatches.isEmpty then
    return .error <| qualifiedNameCollisionError entry.registrationModuleName
      entry.effectiveCatalogId entry.realizationName (realizationMatches.push entry)
  return .ok ()

/-- Validate an entry already stored in the persistent registry exactly once. -/
def validatePersistedEntry (rootId : Name) (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  let entries := InformationRegistry.forRoot env rootId
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  let [stored] := occurrenceMatches.toList
    | return .error (duplicateRegistrationError entry occurrenceMatches)
  unless sameEntry stored entry do
    return .error "P1.CertificateBindingMismatch: supplied entry differs from authoritative raw row"
  -- Only the authoritative row determines whether derived checks are required.
  let entry := stored
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  try
    if entry.derivedCertificate.isSome then RegistrationReifier.closedTruthExcluded entry
  catch e => return .error (← e.toMessageData.toString)
  let unitMatches := entries.filter fun candidate => candidate.unitName == entry.unitName
  match unitMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error <| qualifiedNameCollisionError entry.registrationModuleName
        entry.effectiveCatalogId entry.unitName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError entry.registrationModuleName
      entry.effectiveCatalogId entry.unitName unitMatches)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  match realizationMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error <| qualifiedNameCollisionError entry.registrationModuleName
        entry.effectiveCatalogId entry.realizationName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError entry.registrationModuleName
      entry.effectiveCatalogId entry.realizationName realizationMatches)
  return .ok ()



def registerSemanticEntry (rootId : Name) (entry : InformationRegistryEntry) :
    Lean.Elab.Command.CommandElabM InformationRegistryEntry := do
  let env ← getEnv
  let entry ← if entry.resolvedArenaName.isAnonymous then
      Lean.Elab.Command.liftTermElabM <| prepareRegistrationEntry rootId env entry
    else pure entry
  let entry := { entry with statementIdentity := if entry.statementIdentity.isEmpty then
    theoremStatementIdentity env entry.theoremName else entry.statementIdentity }
  let result <- Lean.Elab.Command.liftTermElabM <|
    validateNewEntry rootId (← getEnv) entry
  match result with
  | .ok () =>
    Lean.Elab.Command.liftTermElabM do
      let diagnostic ← if entry.sourceBound then pure none else RegistrationGates.validateFinite entry
      let type := (← getConstInfo entry.realizationName).type
      if type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization &&
          diagnostic.isSome then
        throwError "unclassified_form:dtr.forward_bridge_requires_sensitivity: {diagnostic.get!}"
      if type.isAppOfArity RegistrationElaboration.witnessBridgeName 3 then
        if let some diagnostic := diagnostic then throwError diagnostic
      if entry.derivedCertificate.isSome && diagnostic.isSome then
        RegistrationReifier.checkDiagnostic diagnostic.get!
      RegistrationGates.publishDiagnostic entry.registrationModuleName entry.unitName diagnostic
    modifyEnv fun env => informationRegistryExt.modifyState env fun state => {
      entries := state.entries.push entry, theoremNames := state.theoremNames.insert entry.theoremName }
    return entry
  | .error message => throwError message

end LeanInformationAudit
