import LeanInformationAudit.Census.Publish

open Lean Lean.Elab.Command LeanInformationAudit

run_cmd do
  IO.FS.withTempDir fun directory => do
    let env ← CensusProjection.elaborateFinalSource
      "module\npublic import LeanInformationAudit.Census.Certificate\n"
      (directory / "FinalEnvironment.lean").toString `FinalEnvironment {}
    liftTermElabM <| CensusProjection.checkFinalEnvironment env (some `FinalEnvironment)
