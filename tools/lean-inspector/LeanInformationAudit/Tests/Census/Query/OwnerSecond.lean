import LeanInformationAudit.Tests.Census.Query.OwnerSource

run_cmd Lean.Elab.Command.liftTermElabM do
  let some _ <- Lean.Meta.mkCongrSimpForConst?
      `LeanInformationAudit.Tests.Census.Query.ownerParent []
    | throwError "ownerMembershipPositive: reserved lemma was not realized"
