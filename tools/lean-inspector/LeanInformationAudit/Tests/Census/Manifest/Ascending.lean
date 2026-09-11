import LeanInformationAudit.Census.Manifest

open Lean Meta Elab.Command LeanInformationAudit CensusManifest

-- These hit the kernel conjunct directly. The publication binder also rejects
-- the altered chunks before publication, against its wire authorities.
run_cmd do
  liftTermElabM do
    for (label, values) in [
        ("idsReorderedInsideChunk", decodeIds 2 1),
        ("duplicatedIdAcrossChunks", decodeIds 1 1 ++ decodeIds 1 1)] do
      let ids := toExpr values
      let rejected ← try
        discard <| certificateProof ids values.length ids
        pure false
      catch _ => pure true
      unless rejected do throwError "{label}: strictlyAscending conjunct accepted bad ids"
