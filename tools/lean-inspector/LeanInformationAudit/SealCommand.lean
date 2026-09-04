import LeanInformationAudit.ProofBuilder

namespace LeanInformationAudit

open Lean
open Lean.Elab.Command

private def theoremJson (record : SealTheoremRecord) : Json :=
  Json.mkObj [
    ("theorem", record.theoremName.toString),
    ("index", record.index),
    ("unique_capture_count", record.uniqueCaptureCount),
    ("full_escape_count", record.fullEscapeCount),
    ("without_escape_count", record.withoutEscapeCount),
    ("proof_method", record.proofMethod)
  ]

private def arenaJson (record : SealArenaRecord) : Json :=
  Json.mkObj [
    ("arena", record.catalog.arenaName.toString),
    ("catalog", record.catalog.catalogName.toString),
    ("state_card", record.stateCard),
    ("theorems", Json.arr <| record.theorems.map theoremJson)
  ]

private def artifactJson (records : Array SealArenaRecord) : Json :=
  Json.mkObj [
    ("schema", "lean-intrinsic-information-escape-v2"),
    ("arenas", Json.arr <| records.map arenaJson),
    ("role_signature_histogram", Json.null)
  ]

private def logSummary (record : SealArenaRecord) : CommandElabM Unit := do
  for theorem in record.theorems do
    logInfo
      "information seal: arena={record.catalog.arenaName} \
theorem={theorem.theoremName} unique={theorem.uniqueCaptureCount} \
method={theorem.proofMethod}"

syntax (name := sealInformationTheoryCmd)
  "#seal_information_theory" (" output " str)? : command

@[command_elab sealInformationTheoryCmd]
private def elabSealInformationTheory : CommandElab := fun stx => do
  let catalogs ← buildCatalogs
  let records ← buildProofs catalogs
  records.forM logSummary
  if stx.getNumArgs == 3 then
    let path := stx[2].isStrLit?.get!
    liftIO <| IO.FS.writeFile path (artifactJson records).pretty

end LeanInformationAudit
