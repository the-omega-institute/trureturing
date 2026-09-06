import LeanInformationAudit.Tests.Occurrence.RootCausalFixture

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.RootCausalFixture

set_option maxRecDepth 100000

run_cmd registerCausalFixture

set_option maxHeartbeats 8000000 in
-- Construct and kernel-check the complete thirteen-occurrence seal in one command.
run_cmd do
  let originalModule := (← getEnv).header.mainModule
  modifyEnv (·.setMainModule designatedInformationRootId)
  try
    elabCommand (← `(command| #seal_information_theory))
    if (← get).messages.hasErrors then return
    let env ← getEnv
    if (SealRecords.analysisForRoot? env designatedInformationRootId).isSome ||
        env.contains (designatedInformationRootId.str "__system_catalog_irredundant") then
      throwError "DesignatedRootSeal closure contains analysis staging"
    let actual := SealRecords.occurrencesForRoot env designatedInformationRootId
    let expected := expectedOccurrencesForRoot env designatedInformationRootId
    unless actual.size == 13 && expected.size == 13 do
      throwError "ROOT-B-designated-seal: expected actual=expected=13"
    let causal := actual.filter (fun row => row.registrationModuleName ==
      `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration)
    let causalArena :=
      `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena
    unless causal.size == 2 && causal.all (fun row =>
        row.catalogId == `«causal-unified-transitions» && row.objectArenaName == causalArena) do
      throwError "ROOT-B-designated-seal: causal contributor/catalog identity mismatch"
    unless SealRecords.systemCatalogIrredundant env designatedInformationRootId do
      throwError "ROOT-B-designated-seal: system_catalog_irredundant lacks staged proofs"
    for record in SealRecords.forRoot env designatedInformationRootId do
      let some (.thmInfo _) := env.find? record.irredundantCertificateName
        | throwError "ROOT-B-designated-seal: irredundancy certificate is not a theorem"
      elabCommand (← `(command| #print axioms $(mkIdent record.irredundantCertificateName)))
    logInfo "ROOT-B-designated-seal: actual=expected=13 system_catalog_irredundant=true"
  finally
    modifyEnv (·.setMainModule originalModule)
