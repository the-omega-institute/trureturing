import LeanInformationAudit.RegistryTypes
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.Sha256
import LeanInformationAudit.FixedSnapshot
import LeanInformationAudit.FrozenBaseline
import Lean

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

def theoremUnitSuffix := "__information_unit"

def primitiveRealizationSuffix := "__primitive_realization"

def generatedCompanionSuffixes : Array String := #[
  theoremUnitSuffix,
  primitiveRealizationSuffix,
  "__lowers_escape",
  "__escape_enriched",
  "__information_catalog",
  "__catalog_irredundant"
]

def InformationRegistryEntry.lawArenaName (entry : InformationRegistryEntry) : Name :=
  entry.arenaName

def InformationRegistryEntry.canonicalObjectArenaName
    (entry : InformationRegistryEntry) : Name :=
  if !entry.resolvedArenaName.isAnonymous then entry.resolvedArenaName
  else if entry.objectArenaName.isAnonymous then entry.arenaName else entry.objectArenaName

def InformationRegistryEntry.effectiveCatalogId
    (entry : InformationRegistryEntry) : CatalogId :=
  if entry.catalogId.isAnonymous then entry.canonicalObjectArenaName else entry.catalogId

/-- A correctness bound, independent of host speed and caller heartbeat options.
Every head transition, declaration lookup and environment lookup spends one unit. -/
def arenaAliasWorkBudget : Nat := 4096

/-- Elaboration provenance for a structure literal, retained across olean imports.
Lean's structure elaborator eta-contracts field-copy literals before storing them. -/
def arenaConstructionMarker : Name := `LeanInformationAudit.arenaConstruction

private inductive AliasClosure where
  | mk (term : Expr) (bindings : List AliasClosure)

/-- Fuelled weak-head reduction of forwarding aliases only (delta/beta/zeta).
Closures avoid substitution and never traverse or normalize argument subtrees.
Unlike unrestricted `whnfR`, this stops at constructors, projections and recursors,
and never performs structure eta. A bare named target becomes the next owner;
an application that constructs a value retains the last named owner.
The single budget covers both outer aliases and all work inside applications. -/
def resolveCanonicalArenaName (spelling : Name) : MetaM Name := do
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
      | some (.defnInfo info) => current := .mk info.value []
      | _ => return owner
    | _ => return owner
  throwError "IE-C003 ArenaResolutionBudgetExceeded arena={spelling} limit={arenaAliasWorkBudget}"

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

def frozenInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.InformationRoot

def designatedInformationRootId : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot

private def snapshotExpectations (rootId : Name) (rows : Array SnapshotOccurrence) :
    Array ExpectedOccurrence :=
  rows.map fun row => {
    rootId
    objectArenaName := row.objectArenaName
    theoremName := row.theoremName
    statementIdentity := row.statementIdentity
    registrationModuleName := row.registrationModuleName
  }

/-- Read-only expectations captured by SnapshotEnumerator, independently of the root. -/
def fixedSnapshotOccurrences (rootId : Name) : Array ExpectedOccurrence :=
  snapshotExpectations rootId fixedInformationSourceSnapshot.occurrences

/-- The historical frozen root is independent of future source snapshot generation. -/
def frozenBaselineOccurrences (rootId : Name) : Array ExpectedOccurrence :=
  snapshotExpectations rootId frozenInformationRootBaseline

/-- Resolve the independent expectation source for one sealing root. -/
def expectedOccurrencesForRoot (env : Environment) (rootId : Name) :
    Array ExpectedOccurrence :=
  if rootId == frozenInformationRootId then
    frozenBaselineOccurrences rootId
  else if rootId == designatedInformationRootId then
    fixedSnapshotOccurrences rootId
  else
    ExpectedOccurrenceManifest.declaredEntries env rootId

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
    let arenaType <- instantiateMVars (← whnfR (← inferType arenaExpr))
    unless arenaType.getAppFn.constName? == some primitiveLawArenaName do
      return .error s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
    let expectedArena <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
      #[arenaExpr]
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
        #[arenaExpr, realizationExpr]
      unless ← isDefEq theoremType expectedLaw do
        return .error (statementMismatchError entry.theoremName)
      let primitivesExpr <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
        #[unitExpr]
      let compiledBundle <- compilePrimitiveBundle arenaExpr realizationExpr
      unless ← isDefEq primitivesExpr compiledBundle do
        return .error (statementMismatchError entry.theoremName)
    else if realizationHead == some legacyPrimitiveRealizationName then
      match env.find? entry.realizationName with
      | some (.thmInfo _) =>
        let legacyArgs := realizationType.getAppArgs
        unless legacyArgs.size == 3 do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[0]! arenaExpr do
          return .error (statementMismatchError entry.theoremName)
        unless ← isDefEq legacyArgs[1]! theoremType do
          return .error (statementMismatchError entry.theoremName)
        let primitivesExpr <- mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
          #[unitExpr]
        let compiledBundle <- compilePrimitiveBundle arenaExpr legacyArgs[2]!
        unless ← isDefEq primitivesExpr compiledBundle do
          return .error (statementMismatchError entry.theoremName)
      | _ => return .error (statementMismatchError entry.theoremName)
    else
      return .error (statementMismatchError entry.theoremName)
    return .ok ()
  catch _ =>
    return .error (statementMismatchError entry.theoremName)

private def sameEntry (left right : InformationRegistryEntry) : Bool :=
  left.theoremName == right.theoremName &&
    left.unitName == right.unitName &&
    left.arenaName == right.arenaName &&
    left.realizationName == right.realizationName &&
    left.effectiveCatalogId == right.effectiveCatalogId &&
    left.catalogKind == right.catalogKind &&
    left.registrationModuleName == right.registrationModuleName &&
    left.canonicalObjectArenaName == right.canonicalObjectArenaName &&
    left.statementIdentity == right.statementIdentity &&
    left.localRegistrationNames == right.localRegistrationNames

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
  match ← validateEntryCore env entry with
  | .error message => return .error message
  | .ok () => pure ()
  let entries := InformationRegistry.entries env
  let occurrenceMatches := entries.filter fun candidate =>
    candidate.canonicalObjectArenaName == entry.canonicalObjectArenaName &&
      candidate.theoremName == entry.theoremName
  match occurrenceMatches.toList with
  | [candidate] =>
    unless sameEntry candidate entry do
      return .error (duplicateRegistrationError entry occurrenceMatches)
  | _ => return .error (duplicateRegistrationError entry occurrenceMatches)
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

def registerValidatedEntry (entry : InformationRegistryEntry) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let entry ← if entry.resolvedArenaName.isAnonymous then
      Lean.Elab.Command.liftTermElabM <| prepareRegistrationEntry env entry
    else pure entry
  let entry := { entry with statementIdentity := if entry.statementIdentity.isEmpty then
    theoremStatementIdentity env entry.theoremName else entry.statementIdentity }
  let result <- Lean.Elab.Command.liftTermElabM <|
    validateNewEntry (← getEnv) entry
  match result with
  | .ok () => modifyEnv fun env => informationRegistryExt.addEntry env entry
  | .error message => throwError message

end LeanInformationAudit
