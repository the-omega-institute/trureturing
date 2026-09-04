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

@[command_elab sealInformationTheoryCmd]
private def elabSealInformationTheory : CommandElab := fun stx => do
  let catalogs ← buildCatalogs
  let records ← buildProofs catalogs
  records.forM logSummary
  match stx with
  | `(#seal_information_theory output $path:str) =>
      liftIO <| IO.FS.writeFile path.raw.isStrLit?.get!
        (artifactJson records).pretty
  | _ => pure ()

end LeanInformationAudit
