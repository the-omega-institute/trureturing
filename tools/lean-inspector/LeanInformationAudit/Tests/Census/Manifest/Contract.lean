import LeanInformationAudit.Tests.Census.Manifest.Published

open Lean Meta Elab.Command LeanInformationAudit DispositionCensus CensusManifest

private def zeroId := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def oneId := "sha256:" ++ String.ofList (List.replicate 63 '0') ++ "1"

run_cmd do
  unless decodeStatementId `T zeroId == .ok 0 && decodeStatementId `T oneId == .ok 1 do
    throwError "leadingZeroIdentity: strict codec lost leading zeros"
  let bad := #["SHA256:" ++ (oneId.drop 7).toString,
    "sha256:" ++ String.ofList (List.replicate 64 'A'),
    "sha256:" ++ String.ofList (List.replicate 63 '0'),
    "sha256:" ++ String.ofList (List.replicate 65 '0'),
    (oneId.drop 7).toString, "+" ++ oneId, oneId ++ " ", " " ++ oneId]
  for wire in bad do
    match decodeStatementId `T wire with
    | .error error => unless error.contains "component=statement_id_format" do throwError error
    | .ok _ => throwError "codecRoundTripBinding: strictCodecRejections accepted malformed identity"
  match bindStatementIdNat `T oneId 0 with
  | .error error => unless error.contains "component=statement_id_nat" do throwError error
  | .ok _ => throwError "codecRoundTripBinding: a second wire identity bound to zero"

private def report : FrozenReport :=
  { headSha := "head", reportSha256 := "digest", theorems := #[⟨`T, zeroId⟩, ⟨`U, oneId⟩] }

private def manifest : CensusKeyManifest :=
  ⟨"head", "digest", `Root, [0, 1]⟩

run_cmd do
  let keys := report.theorems
  ofExcept <| checkManifestBinding report `Root keys manifest manifest.keys
  for (label, candidate, reportKeys) in #[
      ("manifestDetachedFromRows", { manifest with keys := [0, 2] }, manifest.keys),
      ("reflexiveReportRejected", { manifest with keys := [0, 2] }, [0, 2]),
      ("staleManifestHead", { manifest with headSha := "stale" }, manifest.keys),
      ("wrongManifestDigest", { manifest with reportSha256 := "wrong" }, manifest.keys),
      ("manifestNatBinding", { manifest with keys := [1, 2] }, manifest.keys)] do
    match checkManifestBinding report `Root keys candidate reportKeys with
    | .error _ => pure ()
    | .ok _ => throwError "{label}: detached certificate accepted"
  match checkManifestBinding report `Root (keys.extract 0 1)
      { manifest with keys := [0] } manifest.keys with
  | .error error => unless error.startsWith "IE-C034" do throwError error
  | .ok _ => throwError "deletedManifestRow: deleted row accepted"

run_cmd do
  liftTermElabM do
    let ids := toExpr manifest.keys
    let proof ← try certificateProof ids 2 ids
      catch error => throwError "certificateAscendingConjunct: {error.toMessageData}"
    let expected ← Elab.Term.elabTerm (← `(strictlyAscending manifest.keys = true ∧
      manifest.keys.length = 2 ∧ manifest.keys = manifest.keys)) none
    unless ← isDefEq (← inferType proof) expected do
      throwError "certificateAscendingConjunct: certificate type lost a conjunct"
    checkWithKernel proof
    let detached := toExpr ([0, 2] : List Nat)
    let rejected ← try
      discard <| certificateProof ids 2 detached
      pure false
    catch _ => pure true
    unless rejected do throwError "reportListEqualityBinding: inventory copied to report side"

-- Finset reasoning stays outside the final environment, over the id set only.
example : CensusKeyManifest.IdCoverage manifest.keys 2 manifest.keys.toFinset :=
  CensusKeyManifest.idCoverage_of_certificate _ _ _ ⟨by decide, rfl, rfl⟩

example : strictlyAscending [0, 1, 2] = true := by decide
example : strictlyAscending [0, 0] = false := by decide
example : strictlyAscending [1, 0] = false := by decide
example : decodeIds 2 (2 ^ 256) = [0, 1] := by decide +kernel
example : decodeIds 2 1 = [1, 0] := by decide +kernel

run_cmd LeanInformationAudit.Tests.Census.Manifest.checkPublishedCertificate "certificateAscendingConjunct"
