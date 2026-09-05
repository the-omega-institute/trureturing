import LeanInformationAudit.ProofBuilder
import LeanInformationAudit.Syntax

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
    ("certificate", record.theoremName.str "__lowers_escape" |>.toString),
    ("proof_method", record.proofMethod)
  ]

private def occurrenceJson (rootId : Name) (catalogId : CatalogId)
    (denominator : Nat) (record : SealTheoremRecord) : Json :=
  Json.mkObj [
    ("theorem", record.theoremName.toString),
    ("catalog_membership", Json.mkObj [
      ("root_id", rootId.toString),
      ("catalog_id", catalogId.toString)
    ]),
    ("unit", record.unitName.toString),
    ("primitive_count", record.primitiveCount),
    ("primitive_axes", Json.arr <| record.primitiveAxes.map Json.str),
    ("primitive_kernel_address", record.primitiveKernelAddress),
    ("full_escape_count", record.fullEscapeCount),
    ("without_escape_count", record.withoutEscapeCount),
    ("unique_capture_count", record.uniqueCaptureCount),
    ("unique_capture_by_role_signature", Json.mkObj <|
      record.roleSignatureHistogram.toList.map fun entry =>
        (entry.1, toJson entry.2)),
    ("gain_rate", rateJson record.uniqueCaptureCount denominator),
    ("lowers_escape", true),
    ("certificate", record.certificateName.toString)
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
    ("schema", "lean-intrinsic-information-escape-v2"),
    ("catalog_mode", "single-compilation-leave-one-out"),
    ("arenas", Json.arr <| records.map arenaJson)
  ]

private def v3VerdictCertificate (record : SealArenaRecord) : Name :=
  catalogQualifiedName record.catalog.rootId record.catalog.arenaName
    record.catalog.catalogId record.catalog.arenaName "__catalog_irredundant"

private def catalogJsonV3 (record : SealArenaRecord) : Json :=
  Json.mkObj [
    ("catalog_id", record.catalog.catalogId.toString),
    ("catalog_kind", record.catalog.catalogKind.artifactName),
    ("object_arena", record.catalog.arenaName.toString),
    ("proof_method", record.proofMethod),
    ("state_card", record.stateCard),
    ("off_diagonal_pair_count", record.offDiagonalPairCount),
    ("full_escape_count", record.fullEscapeCount),
    ("full_escape_rate", rateJson record.fullEscapeCount
      record.offDiagonalPairCount),
    ("catalog_verdict", "irredundant"),
    ("redundant_theorems", Json.arr #[]),
    ("verdict_certificate", v3VerdictCertificate record |>.toString),
    ("theorems", Json.arr <| record.theorems.map
      (occurrenceJson record.catalog.rootId record.catalog.catalogId
        record.offDiagonalPairCount))
  ]

private def distinctSortedNames (names : Array Name) : Array Name :=
  names.foldl (init := #[]) (fun result name =>
    if result.contains name then result else result.push name)
    |>.qsort fun left right => left.lt right

private def registrationModules (records : Array SealArenaRecord) : Array Name :=
  distinctSortedNames <| records.foldl (init := #[]) fun modules record =>
    modules ++ record.catalog.units.map (·.registrationModuleName)

private def occurrenceQualifiedName (record : SealArenaRecord)
    (theoremRecord : SealTheoremRecord) : Name :=
  catalogQualifiedName record.catalog.rootId record.catalog.arenaName
    record.catalog.catalogId theoremRecord.theoremName "__occurrence"

private def coincidenceClasses (records : Array SealArenaRecord) : Json :=
  let groups := records.foldl (init := #[]) fun groups record =>
    record.theorems.foldl (init := groups) fun groups theoremRecord =>
      let occurrence := occurrenceQualifiedName record theoremRecord
      match groups.findIdx? fun group =>
          group.1 == theoremRecord.primitiveKernelAddress with
      | some index => groups.modify index fun group => (group.1, group.2.push occurrence)
      | none => groups.push (theoremRecord.primitiveKernelAddress, #[occurrence])
  let collisions := groups.filter (fun group => group.2.size > 1)
    |>.qsort fun left right => left.1 < right.1
  Json.arr <| collisions.map fun group => Json.mkObj [
    ("primitive_kernel_address", group.1),
    ("occurrences", Json.arr <| (group.2.qsort fun left right => left.lt right).map
      (fun name => Json.str name.toString)),
    ("serializer", "primitive-kernel-classes-v1"),
    ("diagnostic_only", true)
  ]

private def artifactJsonV3 (records : Array SealArenaRecord) : Json :=
  let rootId := records[0]? |>.map (·.catalog.rootId) |>.getD .anonymous
  Json.mkObj [
    ("schema", "lean-intrinsic-information-escape-v3"),
    ("root_id", rootId.toString),
    ("seal_scope", "import-closure"),
    ("registration_modules", Json.arr <|
      (registrationModules records).map fun name => Json.str name.toString),
    ("system_catalog_irredundant", true),
    ("kernel_address_coincidence_classes", coincidenceClasses records),
    ("catalogs", Json.arr <| records.map catalogJsonV3)
  ]

private def sealArtifactJson (records : Array SealArenaRecord) : Json :=
  if records.all (·.catalog.compatibilityV2) then artifactJson records
  else artifactJsonV3 records

private def logSummary (record : SealArenaRecord) : CommandElabM Unit := do
  for theoremRecord in record.theorems do
    logInfo <| s!
      "information seal: arena={record.catalog.arenaName} \
theorem={theoremRecord.theoremName} unique={theoremRecord.uniqueCaptureCount} \
method={theoremRecord.proofMethod}"

syntax (name := sealInformationTheoryCmd)
  "#seal_information_theory" (" output " str)? : command

private def declarationNames (declarations : Array Declaration) : List Name :=
  declarations.toList.foldl (init := []) fun names declaration =>
    names ++ declaration.getNames

private def catalogForGeneratedName? (records : Array SealArenaRecord) (name : Name) :
    Option SealArenaRecord :=
  records.find? fun record =>
    record.catalog.catalogName == name || v3VerdictCertificate record == name ||
      record.theorems.any fun theoremRecord => theoremRecord.certificateName == name ||
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
          if record.catalog.compatibilityV2 then
            throwError "IE-C009 ProofConstructionFailed: {name}\ngenerated name collision"
          else
            let entries := InformationRegistry.entries env |>.filter fun entry =>
              entry.canonicalObjectArenaName == record.catalog.arenaName
            throwError (qualifiedNameCollisionError record.catalog.rootId
              record.catalog.catalogId name entries)
      | none =>
          throwError "IE-C009 ProofConstructionFailed: {name}\ngenerated name collision"
    seen := seen.push name

private def occurrenceKeyStringsFromRecords (records : Array SealArenaRecord) : Array String :=
  records.foldl (init := #[]) fun keys record =>
    keys ++ record.theorems.map fun theoremRecord =>
      record.catalog.arenaName.toString ++ "/" ++ theoremRecord.theoremName.toString

private def occurrenceKeyStringsFromRegistry (env : Environment) : Array String :=
  InformationRegistry.entries env |>.map fun entry =>
    entry.canonicalObjectArenaName.toString ++ "/" ++ entry.theoremName.toString

private def validateRegistrySnapshot (env : Environment) (records : Array SealArenaRecord) :
    CommandElabM Unit := do
  let expected := occurrenceKeyStringsFromRecords records |>.qsort (· < ·)
  let actual := occurrenceKeyStringsFromRegistry env |>.qsort (· < ·)
  unless expected == actual do
    let rootId := env.header.mainModule
    throwError
      "IE-C028 AnalysisCertificateMismatch root={rootId} catalog=registry-snapshot \
component=member-set expected={(toJson expected).compress} actual={(toJson actual).compress}"

private def stageDeclarations (env : Environment) (declarations : Array Declaration) :
    CommandElabM Environment := do
  let options ← getOptions
  let mut stagedEnv := env
  for declaration in declarations do
    match stagedEnv.addDeclCore (Core.getMaxHeartbeats options).toUSize
        (maxRecDepth.get options).toUSize declaration none true with
    | .ok nextEnv => stagedEnv := nextEnv
    | .error error =>
        let name := declaration.getNames[0]!
        throwError "IE-C009 ProofConstructionFailed: {name}\n{error.toMessageData options}"
  pure stagedEnv

/-! The seal has four phases: validate and prepare catalogs; compute counts and
proof declarations; preflight and kernel-check every declaration in a local persistent
environment; then publish that environment with one `setEnv`. The optional JSON is
written before publication and is output-only: no seal decision reads it back. -/

@[command_elab sealInformationTheoryCmd]
private def elabSealInformationTheory : CommandElab := fun stx => do
  let baseEnv ← getEnv
  let catalogs ← prepareCatalogs
  let proofs ← prepareProofs catalogs
  let declarations := catalogs.map (·.declaration) ++ proofs.declarations
  validateRegistrySnapshot baseEnv proofs.records
  preflightNames baseEnv proofs.records declarations
  let stagedEnv ← stageDeclarations baseEnv declarations
  match stx with
  | `(#seal_information_theory output $path:str) =>
      liftIO <| IO.FS.writeFile path.raw.isStrLit?.get!
        (sealArtifactJson proofs.records).pretty
  | _ => pure ()
  setEnv stagedEnv
  proofs.records.forM logSummary

end LeanInformationAudit
