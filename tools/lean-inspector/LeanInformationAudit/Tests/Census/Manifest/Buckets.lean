import LeanInformationAudit.Tests.Census.Manifest.Published

open Lean Meta Elab.Command LeanInformationAudit CensusManifest

noncomputable def outside.chunk0 : Nat := 1
noncomputable def outside : List Nat := List.flatten [decodeIds 1 outside.chunk0]

run_cmd do
  liftTermElabM do
    let rows : Array StatementKey := #[⟨`T, "sha256:" ++ String.ofList (List.replicate 63 '0') ++ "1"⟩]
    let rejected ← try
      -- The packing matches its wire; only the assigned prefix is wrong.
      discard <| bindChunkedKeys `outside "manifest_keys" rows (some (1, 8))
      pure false
    catch error =>
      unless (← error.toMessageData.toString).contains "component=bucket_prefix" do throw error
      pure true
    unless rejected do throwError "bucketRangeBinding: id assigned to the wrong prefix accepted"

run_cmd LeanInformationAudit.Tests.Census.Manifest.checkPublishedCertificate "bucketEqualityConjunct"
