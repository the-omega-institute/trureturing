import LeanInformationAudit.ProofBuilder
import LeanInformationAudit.Projection.ProjectionSeal
import LeanInformationAudit.Syntax
import LeanInformationAudit.Projection.OutputOnlyAudit

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command

private def rateJson (numerator denominator : Nat) : Json :=
  Json.mkObj [("numerator", numerator), ("denominator", denominator)]

private def theoremJson (denominator : Nat) (record : SealTheoremRecord) : Json :=
  Json.mkObj [
    ("theorem", record.theoremName.toString),
    ("unit", record.unitName.toString),
    ("index", record.index),
    ("primitive_count", record.primitiveCount),
    ("primitive_axes", Json.arr <| record.primitiveAxes.map Json.str),
    ("primitive_kernel_address", record.primitiveKernelAddress),
    ("unique_capture_count", record.uniqueCaptureCount),
    ("full_escape_count", record.fullEscapeCount),
    ("without_escape_count", record.withoutEscapeCount),
    ("unique_capture_by_role_signature", Json.mkObj <|
      record.roleSignatureHistogram.toList.map fun entry =>
        (entry.1, toJson entry.2)),
    ("gain_rate", rateJson record.uniqueCaptureCount denominator),
    ("lowers_escape", true),
    ("certificate", record.certificateName.toString),
    ("proof_method", record.proofMethod)
  ]

private def arenaJson (record : SealArenaRecord) : Json :=
  Json.mkObj [
    ("arena", record.catalog.arenaName.toString),
    ("catalog", record.catalog.catalogName.toString),
    ("state_card", record.stateCard),
    ("off_diagonal_pair_count", record.offDiagonalPairCount),
    ("full_escape_count", record.fullEscapeCount),
    ("full_escape_rate", rateJson record.fullEscapeCount
      record.offDiagonalPairCount),
    ("theorems", Json.arr <|
      record.theorems.map (theoremJson record.offDiagonalPairCount))
  ]

private def artifactJson (records : Array SealArenaRecord) : Json :=
  Json.mkObj [
    ("schema", "lean-intrinsic-information-escape-seal"),
    ("catalog_mode", "single-compilation-leave-one-out"),
    ("arenas", Json.arr <| records.map arenaJson)
  ]

/-- Serialize the catalog and escape-count seal artifact. -/
def serializeSealArtifact (records : Array SealArenaRecord) : String :=
  (artifactJson records).pretty

/-- Fixture-inspectable identity state retained for the later analysis projection. -/
structure SealedOccurrenceState where
  rootId : Name
  catalogId : CatalogId
  objectArenaName : Name
  theoremName : Name
  unitName : Name
  realizationName : Name
  certificateName : Name
  registrationModuleName : Name
  deriving Inhabited, Repr

/-- Projection records retained by explicit staging for a later export command. -/
structure StagedAnalysisState where
  rootId : Name
  records : Array AnalysisCatalogRecord
  systemCertificate : Name
  declarationNames : Array Name
  deriving Inhabited

private initialize sealRecordExt :
    SimplePersistentEnvExtension SealArenaRecord (Array SealArenaRecord) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

private initialize stagedAnalysisExt :
    SimplePersistentEnvExtension StagedAnalysisState (Array StagedAnalysisState) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

namespace SealRecords

def entries (env : Environment) : Array SealArenaRecord :=
  sealRecordExt.getState env

def forRoot (env : Environment) (rootId : Name) : Array SealArenaRecord :=
  entries env |>.filter (·.catalog.rootId == rootId)

def occurrencesForRoot (env : Environment) (rootId : Name) :
    Array SealedOccurrenceState :=
  forRoot env rootId |>.foldl (init := #[]) fun occurrences record =>
    occurrences ++ record.theorems.map fun theoremRecord => {
      rootId := record.catalog.rootId
      catalogId := record.catalog.catalogId
      objectArenaName := record.catalog.arenaName
      theoremName := theoremRecord.theoremName
      unitName := theoremRecord.unitName
      realizationName := theoremRecord.realizationName
      certificateName := theoremRecord.certificateName
      registrationModuleName := theoremRecord.registrationModuleName
    }

def analysisForRoot? (env : Environment) (rootId : Name) : Option StagedAnalysisState :=
  stagedAnalysisExt.getState env |>.find? (·.rootId == rootId)

/-- A root verdict is true only when every retained record names a staged proof. -/
def systemCatalogIrredundant (env : Environment) (rootId : Name) : Bool :=
  let records := forRoot env rootId
  !records.isEmpty && records.all fun record =>
    env.contains record.irredundantCertificateName

end SealRecords

private def logSummary (record : SealArenaRecord) : CommandElabM Unit := do
  for theoremRecord in record.theorems do
    logInfo <| s!
      "information seal: arena={record.catalog.arenaName} \
theorem={theoremRecord.theoremName} unique={theoremRecord.uniqueCaptureCount} \
method={theoremRecord.proofMethod}"

private def declarationNames (declarations : Array Declaration) : List Name :=
  declarations.toList.foldl (init := []) fun names declaration =>
    names ++ declaration.getNames

private def catalogForGeneratedName? (records : Array SealArenaRecord) (name : Name) :
    Option SealArenaRecord :=
  records.find? fun record =>
    record.catalog.catalogName == name || record.irredundantCertificateName == name ||
      record.theorems.any fun theoremRecord => theoremRecord.unitName == name ||
        theoremRecord.realizationName == name || theoremRecord.certificateName == name ||
        catalogQualifiedName record.catalog.rootId record.catalog.arenaName
          record.catalog.catalogId theoremRecord.theoremName "__escape_enriched" == name

private def preflightNames (env : Environment) (records : Array SealArenaRecord)
    (declarations : Array Declaration) :
    CommandElabM Unit := do
  let mut seen : Array Name := #[]
  for name in declarationNames declarations do
    if env.contains name || seen.contains name then
      match catalogForGeneratedName? records name with
      | some record =>
          if record.catalog.localSealNames then
            throwError "IE-C009 ProofConstructionFailed: {name}\ngenerated name collision"
          else
            let entries := InformationRegistry.entries env |>.filter fun entry =>
              entry.canonicalObjectArenaName == record.catalog.arenaName
            throwError (qualifiedNameCollisionError record.catalog.rootId
              record.catalog.catalogId name entries)
      | none =>
          throwError "IE-C009 ProofConstructionFailed: {name}\ngenerated name collision"
    seen := seen.push name

private def expectedKey (entry : ExpectedOccurrence) : String :=
  entry.objectArenaName.toString ++ "/" ++ entry.theoremName.toString

private def actualKey (entry : InformationRegistryEntry) : String :=
  entry.occurrenceKeyString

private def expectedIdentity (entry : ExpectedOccurrence) : String :=
  expectedKey entry ++ "=" ++ entry.statementIdentity

private def actualIdentity (entry : InformationRegistryEntry) : String :=
  actualKey entry ++ "=" ++ entry.statementIdentity

private def expectedContributor (entry : ExpectedOccurrence) : String :=
  expectedKey entry ++ "=" ++ entry.registrationModuleName.toString

private def actualContributor (entry : InformationRegistryEntry) : String :=
  actualKey entry ++ "=" ++ entry.registrationModuleName.toString

private def throwSnapshotMismatch (rootId : Name) (component : String)
    (expected actual : Array String) : CommandElabM Unit :=
  throwError
    "IE-C028 AnalysisCertificateMismatch root={rootId} catalog=registry-snapshot \
component={component} expected={(toJson expected).compress} actual={(toJson actual).compress}"

/-- Fail closed if source snapshot regeneration loses or changes a frozen row.
Uses CIRPT-42 / section 31's IE-C028 payload, as does registry validation below. -/
def validateFrozenBaselineInSnapshot (rootId : Name)
    (snapshot : Array ExpectedOccurrence) : CommandElabM Unit := do
  let baseline := frozenBaselineOccurrences rootId
  let baselineKeys := baseline.map expectedKey |>.qsort (· < ·)
  let retained := snapshot.filter fun row => baselineKeys.contains (expectedKey row)
  let retainedKeys := retained.map expectedKey |>.qsort (· < ·)
  unless baselineKeys == retainedKeys do
    throwSnapshotMismatch rootId "frozen-baseline-member-set" baselineKeys retainedKeys
  let baselineIdentities := baseline.map expectedIdentity |>.qsort (· < ·)
  let retainedIdentities := retained.map expectedIdentity |>.qsort (· < ·)
  unless baselineIdentities == retainedIdentities do
    throwSnapshotMismatch rootId "frozen-baseline-statement-identities"
      baselineIdentities retainedIdentities
  let baselineContributors := baseline.map expectedContributor |>.qsort (· < ·)
  let retainedContributors := retained.map expectedContributor |>.qsort (· < ·)
  unless baselineContributors == retainedContributors do
    throwSnapshotMismatch rootId "frozen-baseline-contributor-modules"
      baselineContributors retainedContributors

/-- Compare the independent root manifest with the sealed import-closure registry. -/
def validateRegistrySnapshot (env : Environment) : CommandElabM Unit := do
  let rootId := env.header.mainModule
  if rootId == frozenInformationRootId || rootId == designatedInformationRootId then
    validateFrozenBaselineInSnapshot rootId (fixedSnapshotOccurrences rootId)
  let expectedEntries := expectedOccurrencesForRoot env rootId
  let actualEntries := InformationRegistry.entries env
  let expectedKeys := expectedEntries.map expectedKey |>.qsort (· < ·)
  let actualKeys := actualEntries.map actualKey |>.qsort (· < ·)
  unless expectedKeys == actualKeys do
    throwSnapshotMismatch rootId "member-set" expectedKeys actualKeys
  let expectedIdentities := expectedEntries.map expectedIdentity |>.qsort (· < ·)
  let actualIdentities := actualEntries.map actualIdentity |>.qsort (· < ·)
  unless expectedIdentities == actualIdentities do
    throwSnapshotMismatch rootId "statement-identities" expectedIdentities actualIdentities
  let expectedContributors := expectedEntries.map expectedContributor |>.qsort (· < ·)
  let actualContributors := actualEntries.map actualContributor |>.qsort (· < ·)
  unless expectedContributors == actualContributors do
    throwSnapshotMismatch rootId "contributor-modules" expectedContributors actualContributors

private def stageDeclarations (env : Environment) (declarations : Array Declaration)
    (minimumHeartbeats : Nat := 0) :
    CommandElabM Environment := do
  let options ← getOptions
  let mut stagedEnv := env
  for declaration in declarations do
    match stagedEnv.addDeclCore
        (max (Core.getMaxHeartbeats options) minimumHeartbeats).toUSize
        (maxRecDepth.get options).toUSize declaration none true with
    | .ok nextEnv => stagedEnv := nextEnv
    | .error error =>
        let name := declaration.getNames[0]!
        throwError "IE-C009 ProofConstructionFailed: {name}\n{error.toMessageData options}"
  pure stagedEnv

private def rootQualifiedEntry (rootId : Name) (localSealNames : Bool)
    (entry : InformationRegistryEntry) : InformationRegistryEntry :=
  if localSealNames then entry else
    { entry with
      unitName := catalogQualifiedName rootId entry.canonicalObjectArenaName
        entry.effectiveCatalogId entry.theoremName theoremUnitSuffix
      realizationName := catalogQualifiedName rootId entry.canonicalObjectArenaName
        entry.effectiveCatalogId entry.theoremName primitiveRealizationSuffix }

private def stageAlias (sourceName targetName : Name) : CommandElabM Unit := do
  let sourceId := mkIdent (`_root_ ++ sourceName)
  let targetId := mkIdent (`_root_ ++ targetName)
  elabCommand (← `(command| abbrev $targetId := $sourceId))

private def prepareRootQualifiedEntries (env : Environment)
    (entries : Array InformationRegistryEntry) :
    CommandElabM (Array (Name × Name) × Array InformationRegistryEntry) := do
  let rootId := env.header.mainModule
  let localSealNames := entries.all fun entry =>
    entry.localRegistrationNames && entry.registrationModuleName == rootId
  let qualified := entries.map (rootQualifiedEntry rootId localSealNames)
  for entry in qualified do
    for generatedName in #[entry.unitName, entry.realizationName] do
      let owners := qualifiedNameCollisionEntries (entries ++ qualified) generatedName entry
      let sourceOwner := entries.any fun candidate =>
        (candidate.unitName == generatedName || candidate.realizationName == generatedName) &&
          candidate.occurrenceKey == entry.occurrenceKey
      if owners.size > 1 || (env.contains generatedName && !sourceOwner) then
        throwError (qualifiedNameCollisionError rootId entry.effectiveCatalogId
          generatedName owners)
  let mut aliases := #[]
  for (source, target) in entries.zip qualified do
    if source.realizationName != target.realizationName then
      aliases := aliases.push (source.realizationName, target.realizationName)
    if source.unitName != target.unitName then
      aliases := aliases.push (source.unitName, target.unitName)
  pure (aliases, qualified)

private def retainSealRecords (env : Environment) (records : Array SealArenaRecord) :
    Environment :=
  records.foldl (init := env) fun current record => sealRecordExt.addEntry current record

private def retainAnalysisState (env : Environment) (state : StagedAnalysisState) : Environment :=
  stagedAnalysisExt.addEntry env state

/-! Seal validates the registry, prepares catalogs and escape-count certificates,
kernel-checks them locally, and publishes SealRecords. Analysis is staged separately.
Neither publication command has an artifact selector or destination. -/

def prepareSealPublication : CommandElabM Unit := do
  let baseEnv ← getEnv
  try
    validateRegistrySnapshot baseEnv
    let sourceEntries := InformationRegistry.entries baseEnv
    validateSourceEntries baseEnv sourceEntries
    let (aliases, catalogEntries) ←
      prepareRootQualifiedEntries baseEnv sourceEntries
    for pair in aliases do
      stageAlias pair.1 pair.2
    let aliasEnv ← getEnv
    let catalogs ← prepareCatalogsFromEntries sourceEntries catalogEntries
    let proofs ← prepareProofs catalogs
    let declarations := catalogs.map (·.declaration) ++ proofs.declarations
    preflightNames aliasEnv proofs.records declarations
    let stagedEnv ← stageDeclarations (← getEnv) declarations
    let stagedEnv := retainSealRecords stagedEnv proofs.records
    proofs.records.forM logSummary
    setEnv stagedEnv
  catch error =>
    setEnv baseEnv
    throw error

/-- Stage analysis for an already-sealed root, publishing only after all checks pass. -/
def prepareInformationAnalysisStage (rootId : Name) : CommandElabM Unit := do
  let sealedEnv ← getEnv
  unless SealRecords.systemCatalogIrredundant sealedEnv rootId do
    throwError "UnsealedAnalysisStage root={rootId} catalog=system"
  if (SealRecords.analysisForRoot? sealedEnv rootId).isSome then
    throwError "AnalysisAlreadyStaged root={rootId} catalog=system"
  try
    let records := SealRecords.forRoot sealedEnv rootId
    let analysis ← prepareAnalysisProofs rootId records
    preflightNames sealedEnv records analysis.declarations
    let stagedEnv ← stageDeclarations (← getEnv) analysis.declarations analysisMaxHeartbeats
    setEnv <| retainAnalysisState stagedEnv {
      rootId
      records := analysis.records
      systemCertificate := analysis.systemCertificate
      declarationNames := declarationNames analysis.declarations |>.toArray
    }
  catch error =>
    setEnv sealedEnv
    throw error

/-- Prepare bytes exclusively from previously staged records and certificates. -/
def prepareInformationAnalysisExport (rootId : Name) (requested : List ArtifactKind) :
    CommandElabM AnalysisExportPlan := do
  let env ← getEnv
  let some analysis := SealRecords.analysisForRoot? env rootId
    | throwError "UnstagedAnalysisExport root={rootId} catalog=system"
  let records := SealRecords.forRoot env rootId
  unless !records.isEmpty && env.contains analysis.systemCertificate do
    throwError "UnstagedAnalysisExport root={rootId} catalog=system"
  let mut artifacts := []
  if requested.contains .seal then
    artifacts := artifacts ++ [(.seal, serializeSealArtifact records)]
  if requested.contains .analysis then
    let contents ← liftTermElabM do
      serializeAnalysisArtifact rootId analysis.records analysis.systemCertificate
    artifacts := artifacts ++ [(.analysis, contents)]
  if requested.contains .ascii then
    let contents ← match serializeAsciiArtifact analysis.records with
      | .ok contents => pure contents
      | .error message => throwError message
    artifacts := artifacts ++ [(.ascii, contents)]
  return { artifacts }

private def elabSealInformationTheory : CommandElab :=
  terminalSealCommand prepareSealPublication

@[command_elab sealInformationTheoryCmd]
private def elabAuditedSeal : CommandElab := fun stx => do
  let currentEnv ← getEnv
  match auditSealOutputOnly currentEnv ``elabSealInformationTheory
      currentEnv.header.mainModule with
  | .error message => throwError message
  | .ok () => elabSealInformationTheory stx

private def elabInformationAnalysisExport : CommandElab :=
  terminalInformationAnalysisExportCommand prepareInformationAnalysisExport

private def elabInformationAnalysisStage : CommandElab :=
  terminalInformationAnalysisStageCommand prepareInformationAnalysisStage

@[command_elab stageInformationAnalysisCmd]
private def elabAuditedInformationAnalysisStage : CommandElab := fun stx => do
  let currentEnv ← getEnv
  match auditInformationAnalysisStage currentEnv ``elabInformationAnalysisStage
      currentEnv.header.mainModule with
  | .error message => throwError message
  | .ok () => elabInformationAnalysisStage stx

@[command_elab exportInformationAnalysisCmd]
private def elabAuditedInformationAnalysisExport : CommandElab := fun stx => do
  let currentEnv ← getEnv
  match auditInformationAnalysisExport currentEnv ``elabInformationAnalysisExport
      currentEnv.header.mainModule with
  | .error message => throwError message
  | .ok () => elabInformationAnalysisExport stx

end LeanInformationAudit
