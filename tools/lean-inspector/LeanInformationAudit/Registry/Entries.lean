import LeanInformationAudit.Registry.Reifier
import LeanInformationAudit.FixedSnapshot
import LeanInformationAudit.FrozenBaseline
import LeanInformationAudit.Registry.ArenaProvenance

namespace LeanInformationAudit

open Lean
open Lean.Meta

def frozenInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.InformationRoot

def designatedInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot

/-- Current production contracts. These rows are content inputs, independent of
registry output; migration moves their suppliers into Reg with their roots. -/
def currentRootCatalogContracts : Array RootCatalogContract := #[
  { rootId := frozenInformationRootId
    expected := frozenInformationRootBaseline
    source := fixedInformationSourceSnapshot.occurrences
    baseline := frozenInformationRootBaseline
    companionPrefix := some .anonymous },
  { rootId := designatedInformationRootId
    expected := fixedInformationSourceSnapshot.occurrences
    source := fixedInformationSourceSnapshot.occurrences
    baseline := frozenInformationRootBaseline }]

private initialize rootCatalogExt :
    SimplePersistentEnvExtension RootCatalogContract (Array RootCatalogContract) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) currentRootCatalogContracts }



private def theoremUnitName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

private def primitiveLawArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena

private def primitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization

private def legacyPrimitiveRealizationName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization

def theoremUnitSuffix := "__information_unit"

def primitiveRealizationSuffix := "__primitive_realization"

def generatedCompanionSuffixes : Array String := #[
  theoremUnitSuffix,
  primitiveRealizationSuffix,
  "__lowers_escape",
  "__trivial_in_catalog",
  "__escape_enriched",
  "__information_catalog",
  "__catalog_irredundant",
  "__catalog_redundant",
  "__system_catalog_irredundant",
  "__system_catalog_not_irredundant",
  "__information_registration_diagnostic"
]

def InformationRegistryEntry.lawArenaName (entry : InformationRegistryEntry) : Name :=
  entry.arenaName

/-- A correctness bound, independent of host speed and caller heartbeat options.
Every head transition, declaration lookup and environment lookup spends one unit. -/
def arenaAliasWorkBudget : Nat := 4096

/-- Elaboration provenance for a structure literal, retained across olean imports.
Lean's structure elaborator eta-contracts field-copy literals before storing them. -/
def arenaConstructionMarker : Name := ArenaProvenance.construction

private inductive AliasClosure where
  | mk (term : Expr) (bindings : List AliasClosure)

/-- Fuelled weak-head reduction of forwarding aliases only (delta/beta/zeta).
Closures avoid substitution and never traverse or normalize argument subtrees.
Unlike unrestricted `whnfR`, this stops at constructors, projections and recursors,
and never performs structure eta. A bare named target becomes the next owner;
an application that constructs a value retains the last named owner.
The single budget covers both outer aliases and all work inside applications. -/
private def resolveCanonicalArenaUsing (declarationValue : DefinitionVal → MetaM Expr)
    (spelling : Name) : MetaM Name := do
  let env ← getEnv
  unless env.contains spelling do return spelling
  let mut owner := spelling
  let mut current := AliasClosure.mk (mkConst spelling) []
  let mut arguments : List AliasClosure := []
  let mut fuel := arenaAliasWorkBudget
  while fuel > 0 do
    fuel := fuel - 1
    let .mk term bindings := current
    match term with
    | .mdata data body =>
      if data.contains arenaConstructionMarker then return owner
      if data.contains ArenaProvenance.unsupported then
        throwError "IE-C003 ArenaSourceUnsupported arena={spelling} owner={owner}"
      current := .mk body bindings
    | .app fn arg =>
      arguments := .mk arg bindings :: arguments
      current := .mk fn bindings
    | .letE _ _ value body _ =>
      current := .mk body (.mk value bindings :: bindings)
    | .lam _ _ body _ =>
      match arguments with
      | [] => return owner
      | arg :: rest =>
        arguments := rest
        current := .mk body (arg :: bindings)
    | .bvar index =>
      match bindings with
      | [] => throwError "IE-C003 ArenaResolutionFailed: {spelling}"
      | value :: rest =>
        current := if index == 0 then value else .mk (.bvar (index - 1)) rest
    | .const name _ =>
      if arguments.isEmpty then owner := name
      match env.find? name with
      | some (.defnInfo info) => current := .mk (← declarationValue info) []
      | _ => return owner
    | _ => return owner
  throwError "IE-C003 ArenaResolutionBudgetExceeded arena={spelling} limit={arenaAliasWorkBudget}"

/-- Acquire source construction evidence while compiling a registration. -/
def resolveCanonicalArenaName : Name → MetaM Name :=
  resolveCanonicalArenaUsing ArenaProvenance.declarationValue

/-- Validate imported registrations using only their compiled provenance. -/
def resolveCanonicalArenaNameFromEvidence : Name → MetaM Name :=
  resolveCanonicalArenaUsing ArenaProvenance.compiledValue

namespace RootCatalogs

/-- Acquire all independent inputs while compiling a contract. A source or baseline
row need not be registered or expected. Keep the supplied identities and membership
unchanged; only the compiler's provenance extension receives evidence. -/
def acquireProvenance (contract : RootCatalogContract) : MetaM Unit := do
  for row in contract.expected ++ contract.source ++ contract.baseline do
    discard <| resolveCanonicalArenaName row.objectArenaName

/-- The retained default roots may seal without a declaration command. Their
contributors acquire the independent inputs available in their compilation;
ordinary imports carry that evidence to the later root. Missing declarations
remain missing and are rejected by the existing seal membership checks. -/
def acquireSeededProvenance : MetaM Unit := do
  for contract in currentRootCatalogContracts do
    acquireProvenance contract

def find? (env : Environment) (rootId : Name) : Option RootCatalogContract :=
  (rootCatalogExt.getState env).find? (·.rootId == rootId)

/-- A root declares its contract before registering/sealing. Imported contracts
remain keyed by their original root and cannot change a downstream root. -/
def declare (contract : RootCatalogContract) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless contract.rootId == env.header.mainModule do
    throwError "IE-C028 RootContractOwnerMismatch: {contract.rootId}"
  if (find? env contract.rootId).isSome then
    throwError "IE-C028 DuplicateRootContract: {contract.rootId}"
  Elab.Command.liftTermElabM <| acquireProvenance contract
  modifyEnv fun current =>
    let current := match contract.companionPrefix with
      | some companionPrefix => current.registerNamespace companionPrefix
      | none => current
    rootCatalogExt.addEntry current contract

end RootCatalogs

def InformationRegistryEntry.occurrenceKey
    (entry : InformationRegistryEntry) : Name × Name :=
  (entry.canonicalObjectArenaName, entry.theoremName)

/-- The naming function used for all occurrence-qualified companions. -/
def catalogQualifiedName (rootId objectArenaName : Name) (catalogId : CatalogId)
    (theoremName : Name) (suffix : String) : Name :=
  theoremName
    |>.str (rootId.toString ++ "/" ++ objectArenaName.toString ++ "/" ++
      catalogId.toString)
    |>.str suffix

private def jsonStringArray (values : Array String) : String :=
  (Json.arr <| values.map Json.str).compress

def InformationRegistryEntry.occurrenceKeyString
    (entry : InformationRegistryEntry) : String :=
  entry.canonicalObjectArenaName.toString ++ "/" ++ entry.theoremName.toString

def qualifiedNameCollisionError (rootId : Name) (catalogId : CatalogId)
    (generatedName : Name) (entries : Array InformationRegistryEntry) : String :=
  let occurrences := entries.map (·.occurrenceKeyString) |>.toList.eraseDups.toArray
    |>.qsort (· < ·)
  s!"IE-C025 QualifiedNameCollision root={rootId} catalog={catalogId} \
generated_name={generatedName} occurrences={jsonStringArray occurrences}"

def qualifiedNameCollisionEntries (entries : Array InformationRegistryEntry)
    (generatedName : Name) (prospective : InformationRegistryEntry) :
    Array InformationRegistryEntry :=
  let owners := (entries.filter fun entry =>
    entry.unitName == generatedName || entry.realizationName == generatedName).push prospective
  owners.foldl (init := #[]) (fun result entry =>
    if result.any (fun owner => owner.occurrenceKey == entry.occurrenceKey) then result
    else result.push entry)
    |>.qsort (fun left right => left.occurrenceKeyString < right.occurrenceKeyString)

def rejectKernelAddressSemanticUse (rootId : Name) (catalogId : CatalogId)
    (address consumer : String) : Except String Unit :=
  .error s!"IE-C030 KernelAddressUsedAsSemanticEvidence root={rootId} \
catalog={catalogId} address={address} consumer={consumer}"

private initialize informationRegistryExt :
    SimplePersistentEnvExtension InformationRegistryEntry
      (Array InformationRegistryEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

def InformationRegistry.entries (env : Environment) :
    Array InformationRegistryEntry :=
  informationRegistryExt.getState env

def InformationRegistry.find? (env : Environment) (theoremName : Name) :
    Option InformationRegistryEntry :=
  (entries env).find? fun entry => entry.theoremName == theoremName

def InformationRegistry.hasTheorem (env : Environment) (n : Name) : Bool :=
  (find? env n).isSome

def InformationRegistry.hasOccurrence (env : Environment)
    (objectArena theoremName : Name) : Bool :=
  (entries env).any fun entry =>
    entry.canonicalObjectArenaName == objectArena && entry.theoremName == theoremName

def InformationRegistry.hasUnit (env : Environment) (n : Name) : Bool :=
  (entries env).any fun entry => entry.unitName == n

/-- A deterministic identity for the theorem type stored in the elaborated environment. -/
def theoremStatementIdentity (env : Environment) (theoremName : Name) : String :=
  match env.find? theoremName with
  | some (.thmInfo info) => "sha256:" ++ Sha256.hex (toString info.type).toUTF8
  | _ => ""

/-- One independently declared row in a sealing root's expected-occurrence manifest. -/
structure ExpectedOccurrence where
  rootId : Name
  objectArenaName : Name
  theoremName : Name
  statementIdentity : String
  registrationModuleName : Name
  deriving Inhabited, Repr

private initialize expectedOccurrenceExt :
    SimplePersistentEnvExtension ExpectedOccurrence (Array ExpectedOccurrence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

namespace ExpectedOccurrenceManifest

def declaredEntries (env : Environment) (rootId : Name) : Array ExpectedOccurrence :=
  expectedOccurrenceExt.getState env |>.filter (·.rootId == rootId)

def addEntry (env : Environment) (entry : ExpectedOccurrence) : Environment :=
  expectedOccurrenceExt.addEntry env entry

end ExpectedOccurrenceManifest

/-- The root contract selects published companion ownership. Without an explicit
prefix, imported objects receive private names local to this compilation. -/
def localCompanionName (env : Environment) (owner : Name) (suffix : String) : Name :=
  let name := owner.str suffix
  if !env.isImportedConst owner then name
  else match (RootCatalogs.find? env env.header.mainModule).bind (·.companionPrefix) with
    | some companionPrefix => companionPrefix ++ name
    | none => mkPrivateName env name

def snapshotExpectations (rootId : Name) (rows : Array SnapshotOccurrence) :
    Array ExpectedOccurrence :=
  rows.map fun row => {
    rootId
    objectArenaName := row.objectArenaName
    theoremName := row.theoremName
    statementIdentity := row.statementIdentity
    registrationModuleName := row.registrationModuleName
  }

/-- Resolve the independent expectation source for one sealing root. -/
def expectedOccurrencesForRoot (env : Environment) (rootId : Name) :
    Array ExpectedOccurrence :=
  match RootCatalogs.find? env rootId with
  | some contract => snapshotExpectations rootId contract.expected
  | none => ExpectedOccurrenceManifest.declaredEntries env rootId

def isCompanionName : Name -> Bool
  | .str _ suffix =>
      generatedCompanionSuffixes.contains suffix
  | _ => false

/-- Complete, deterministic payload shared by prechecks, insertion and sealing.
`entries` contains every contributing registration, including a prospective one
when rejecting insertion; module names are a sorted set, count counts entries. -/
def duplicateRegistrationError (entry : InformationRegistryEntry)
    (entries : Array InformationRegistryEntry) : String :=
  let modules := entries.map (·.registrationModuleName.toString)
    |>.toList.eraseDups.toArray |>.qsort (· < ·)
  s!"IE-C002 DuplicateRegistration object_arena={entry.canonicalObjectArenaName} \
theorem_name={entry.theoremName} registration_modules={jsonStringArray modules} \
count={entries.size}"

/-- Resolve the prospective owner before any admission precheck. -/
def prepareRegistrationEntry (env : Environment)
    (entry : InformationRegistryEntry) : MetaM InformationRegistryEntry := do
  let spelling := if entry.objectArenaName.isAnonymous then entry.arenaName
    else entry.objectArenaName
  let resolvedArenaName ← resolveCanonicalArenaName spelling
  return { entry with
    resolvedArenaName
    registrationModuleName := if entry.registrationModuleName.isAnonymous then
      env.header.mainModule else entry.registrationModuleName }


private def statementMismatchError (name : Name) : String :=
  s!"IE-C006 StatementProofMismatch: {name}"

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
  let arenaExpr := (← RegistrationGates.normalizeArena arenaExpr).law
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
  match validateEntryDeclarations env entry with
  | .error message => return .error message
  | .ok () => pure ()
  try
    if entry.derivedCertificate.isSome then
      let spelling := if entry.objectArenaName.isAnonymous then entry.arenaName
        else entry.objectArenaName
      unless entry.statementIdentity == theoremStatementIdentity env entry.theoremName &&
          entry.resolvedArenaName == (← resolveCanonicalArenaNameFromEvidence spelling) do
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
    let normalized ← RegistrationGates.normalizeArena arenaExpr
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
        realizationHead == some RegistrationGates.witnessBridgeName then
      match env.find? entry.realizationName with
      | some (.thmInfo _) =>
        let legacyArgs := realizationType.getAppArgs
        unless legacyArgs.size == 3 do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[0]! arenaExpr do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[1]! theoremType do
          return .error (statementMismatchError entry.theoremName)
        if realizationHead == some RegistrationGates.witnessBridgeName then
          discard <| RegistrationGates.witnessStatement arenaExpr legacyArgs[1]! entry.theoremName
        let primitivesExpr <- mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
          #[unitExpr]
        let compiledBundle <- compilePrimitiveBundle arenaExpr legacyArgs[2]!
        unless ← isDefEq primitivesExpr compiledBundle do
          return .error (statementMismatchError entry.theoremName)
      | _ => return .error (statementMismatchError entry.theoremName)
    else
      return .error (statementMismatchError entry.theoremName)
    return .ok ()) fun e => do
    if entry.derivedCertificate.isSome && e.isRuntime then
      return .error s!"P1.IncompleteCheck: {← e.toMessageData.toString}"
    return .error (statementMismatchError entry.theoremName)

private def sameCertificate : Option AutoDerivedSemanticCertificate →
    Option AutoDerivedSemanticCertificate → Bool
  | none, none => true
  | some a, some b =>
    a.occurrence == b.occurrence && a.catalogKind == b.catalogKind &&
      a.localRegistrationNames == b.localRegistrationNames && a.statementIdentity == b.statementIdentity &&
      a.levelParams == b.levelParams && a.nondegenerate == b.nondegenerate &&
      a.statement.equal b.statement && a.descriptor.equal b.descriptor &&
      a.arena.equal b.arena && a.outputEvidence.equal b.outputEvidence
  | _, _ => false

def sameEntry (left right : InformationRegistryEntry) : Bool :=
  RegistrationReifier.occurrenceBinding left == RegistrationReifier.occurrenceBinding right &&
    left.catalogKind == right.catalogKind && left.statementIdentity == right.statementIdentity &&
    left.localRegistrationNames == right.localRegistrationNames &&
    sameCertificate left.derivedCertificate right.derivedCertificate

/-- Validate a prospective entry before insertion; neither registry key may exist yet. -/
def validateNewEntry (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  let entries := InformationRegistry.entries env
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  if !occurrenceMatches.isEmpty then
    return .error (duplicateRegistrationError entry (occurrenceMatches.push entry))
  let unitMatches := entries.filter fun candidate =>
    candidate.unitName == entry.unitName
  if !unitMatches.isEmpty then
    return .error <| qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.unitName (unitMatches.push entry)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  if !realizationMatches.isEmpty then
    return .error <| qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.realizationName (realizationMatches.push entry)
  return .ok ()

/-- Validate an entry already stored in the persistent registry exactly once. -/
def validatePersistedEntry (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  let entries := InformationRegistry.entries env
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
      return .error <| qualifiedNameCollisionError env.header.mainModule
        entry.effectiveCatalogId entry.unitName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.unitName unitMatches)
  let realizationMatches := entries.filter fun candidate =>
    candidate.realizationName == entry.realizationName
  match realizationMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error <| qualifiedNameCollisionError env.header.mainModule
        entry.effectiveCatalogId entry.realizationName #[candidate, entry]
  | _ => return .error (qualifiedNameCollisionError env.header.mainModule
      entry.effectiveCatalogId entry.realizationName realizationMatches)
  return .ok ()



def registerSemanticEntry (entry : InformationRegistryEntry) :
    Lean.Elab.Command.CommandElabM InformationRegistryEntry := do
  Elab.Command.liftTermElabM RootCatalogs.acquireSeededProvenance
  let env ← getEnv
  let entry ← if entry.resolvedArenaName.isAnonymous then
      Lean.Elab.Command.liftTermElabM <| prepareRegistrationEntry env entry
    else pure entry
  let entry := { entry with statementIdentity := if entry.statementIdentity.isEmpty then
    theoremStatementIdentity env entry.theoremName else entry.statementIdentity }
  let result <- Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) entry
  match result with
  | .ok () =>
    Lean.Elab.Command.liftTermElabM do
      let diagnostic ← RegistrationGates.validateFinite entry
      let type := (← getConstInfo entry.realizationName).type
      if type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization &&
          diagnostic.isSome then
        throwError "unclassified_form:dtr.forward_bridge_requires_sensitivity: {diagnostic.get!}"
      if type.isAppOfArity RegistrationGates.witnessBridgeName 3 then
        if let some diagnostic := diagnostic then throwError diagnostic
      if entry.derivedCertificate.isSome && diagnostic.isSome then
        RegistrationReifier.checkDiagnostic diagnostic.get!
      RegistrationGates.publishDiagnostic entry.unitName diagnostic
    modifyEnv fun env => informationRegistryExt.addEntry env entry
    return entry
  | .error message => throwError message

end LeanInformationAudit
