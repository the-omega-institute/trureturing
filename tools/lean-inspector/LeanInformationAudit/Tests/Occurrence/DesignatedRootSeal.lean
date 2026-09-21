import D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot

open Lean Lean.Elab.Command LeanInformationAudit

-- Inspect the complete seal published by the real registration owners.
-- Simulating another mainModule cannot supply native occurrence ownership.
run_cmd do
  let env ← getEnv
  if (SealRecords.analysisForRoot? env designatedInformationRootId).isSome ||
      env.contains (designatedInformationRootId.str "__system_catalog_irredundant") then
    throwError "DesignatedRootSeal closure contains analysis staging"
  let actual := SealRecords.occurrencesForRoot env designatedInformationRootId
  let expected := expectedOccurrencesForRoot env designatedInformationRootId
  unless actual.size == 13 && expected.size == 13 do
    throwError "ROOT-B-designated-seal: expected actual=expected=13"
  -- Preserve the production 11/13 source split alongside the generic split test.
  let frozen := expectedOccurrencesForRoot env frozenInformationRootId
  unless frozen.size == 11 && frozen.all (·.registrationModuleName == frozenInformationRootId) do
    throwError "ROOT-B-snapshot-split: production frozen contributor inventory changed"
  let sourceCausal := expected.filter (·.registrationModuleName != frozenInformationRootId)
  unless sourceCausal.size == 2 && sourceCausal.all (fun row =>
      row.objectArenaName ==
        `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena &&
      row.registrationModuleName ==
        `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration) do
    throwError "ROOT-B-snapshot-split: production causal source inventory changed"
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
    let some (.thmInfo _) := env.find? record.verdict.name
      | throwError "ROOT-B-designated-seal: irredundancy certificate is not a theorem"
    elabCommand (← `(command| #print axioms $(mkIdent record.verdict.name)))
  logInfo "ROOT-B-designated-seal: actual=expected=13 system_catalog_irredundant=true"
