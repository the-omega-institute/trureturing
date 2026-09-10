import LeanInformationAudit.Census.Publish

open Lean Meta Elab Command LeanInformationAudit CensusProjection

namespace LeanInformationAudit.Tests.Census.Manifest

/-- Check the published proposition independently of its producer's template. -/
def checkPublishedCertificate (label : String) : CommandElabM Unit :=
  IO.FS.withTempDir fun directory => do
    let input := "module\npublic import LeanInformationAudit.Census.Certificate\npublic section\nopen LeanInformationAudit\n" ++
      "@[expose] noncomputable def PublishedCase.ids : List Nat := List.flatten [[0, 1]]\n" ++
      "@[expose] noncomputable def PublishedCase.reportIds : List Nat := List.flatten [[0, 1]]\n"
    let input := input ++ "public theorem PublishedCase.facts : RangeCertificate 0 2 " ++
      "PublishedCase.ids 2 PublishedCase.reportIds := ⟨(by decide +kernel), (by decide +kernel), " ++
      "rfl, rfl⟩\n"
    let text := certificateSource input `PublishedCase.ids `PublishedCase.reportIds `PublishedCase.proof 2
    let env ← elaborateFinalSource text (directory / "PublishedCase.lean").toString `PublishedCase {}
    liftTermElabM <| checkFinalEnvironment env (some `PublishedCase)
    withEnv env <| liftTermElabM do
      let expected ← mkAppM ``CensusKeyManifest.Certificate
        #[mkConst `PublishedCase.ids, toExpr (2 : Nat), mkConst `PublishedCase.reportIds]
      let proof ← getConstInfo `PublishedCase.proof
      unless ← isDefEq proof.type expected do throwError "{label}: published certificate lost a conjunct"

end LeanInformationAudit.Tests.Census.Manifest
