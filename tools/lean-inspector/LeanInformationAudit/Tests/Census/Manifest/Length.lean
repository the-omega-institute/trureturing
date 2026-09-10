import LeanInformationAudit.Tests.Census.Manifest.Published

open Lean Meta Elab.Command LeanInformationAudit CensusManifest

run_cmd do
  liftTermElabM do
    let ids := toExpr ([0, 1] : List Nat)
    let proof ← try certificateProof ids 2 ids
      catch error => throwError "certificateLengthConjunct: {error.toMessageData}"
    let expected ← Elab.Term.elabTerm (← `(strictlyAscending [0, 1] = true ∧
      ([0, 1] : List Nat).length = 2 ∧ ([0, 1] : List Nat) = [0, 1])) none
    unless ← isDefEq (← inferType proof) expected do
      throwError "certificateLengthConjunct: certificate type lost a conjunct"
    let dropped := toExpr ([0] : List Nat)
    let rejected ← try
      discard <| certificateProof dropped 2 dropped
      pure false
    catch _ => pure true
    unless rejected do throwError "droppedFromBothSides: length conjunct accepted one missing id"

run_cmd LeanInformationAudit.Tests.Census.Manifest.checkPublishedCertificate "certificateLengthConjunct"
