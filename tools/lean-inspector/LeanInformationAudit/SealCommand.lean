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

private def preflightNames (env : Environment) (declarations : Array Declaration) :
    CommandElabM Unit := do
  let mut seen : Array Name := #[]
  for name in declarationNames declarations do
    if env.contains name || seen.contains name then
      throwError "IE-C009 ProofConstructionFailed: {name}\ngenerated name collision"
    seen := seen.push name

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
  preflightNames baseEnv declarations
  let stagedEnv ← stageDeclarations baseEnv declarations
  match stx with
  | `(#seal_information_theory output $path:str) =>
      liftIO <| IO.FS.writeFile path.raw.isStrLit?.get!
        (artifactJson proofs.records).pretty
  | _ => pure ()
  setEnv stagedEnv
  proofs.records.forM logSummary

end LeanInformationAudit
