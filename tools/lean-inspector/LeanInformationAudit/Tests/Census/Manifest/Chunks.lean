import LeanInformationAudit.Census.Manifest

open Lean Meta Elab.Command LeanInformationAudit DispositionCensus CensusManifest

noncomputable def bad.chunk0 : Nat := 1
noncomputable def bad : List Nat := List.flatten [decodeIds 1 bad.chunk0]
noncomputable def good.chunk0 : Nat := 0
noncomputable def good : List Nat := List.flatten [decodeIds 1 good.chunk0]

run_cmd do
  liftTermElabM do
    let rows : Array StatementKey := #[⟨`T, "sha256:" ++ String.ofList (List.replicate 64 '0')⟩]
    discard <| bindChunkedKeys `good "report_keys" rows
    let rejected ← try
      discard <| bindChunkedKeys `bad "report_keys" rows
      pure false
    catch error =>
      unless (← error.toMessageData.toString).contains "component=statement_id_nat" do throw error
      pure true
    unless rejected do throwError "chunkLiteralBinding: changed packed Nat accepted"
