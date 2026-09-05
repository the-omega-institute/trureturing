import LeanInformationAudit.Tests.Occurrence.RootCausalFixture

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.RootCausalFixture

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

run_cmd registerCausalFixture

run_cmd do
  let originalModule := (← getEnv).header.mainModule
  modifyEnv (·.setMainModule designatedInformationRootId)
  try
    elabCommand (← `(command| #seal_information_theory))
    let env ← getEnv
    let actual := SealRecords.occurrencesForRoot env designatedInformationRootId
    let expected := expectedOccurrencesForRoot env designatedInformationRootId
    unless actual.size == 13 && expected.size == 13 do
      throwError "ROOT-B-designated-seal: expected actual=expected=13"
    unless SealRecords.systemCatalogIrredundant env designatedInformationRootId do
      throwError "ROOT-B-designated-seal: system_catalog_irredundant lacks staged proofs"
    for record in SealRecords.forRoot env designatedInformationRootId do
      let some (.thmInfo _) := env.find? record.irredundantCertificateName
        | throwError "ROOT-B-designated-seal: irredundancy certificate is not a theorem"
      elabCommand (← `(command| #print axioms $(mkIdent record.irredundantCertificateName)))
    logInfo "ROOT-B-designated-seal: actual=expected=13 system_catalog_irredundant=true"
  finally
    modifyEnv (·.setMainModule originalModule)
