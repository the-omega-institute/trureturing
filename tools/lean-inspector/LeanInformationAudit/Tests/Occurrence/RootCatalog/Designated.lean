import LeanInformationAudit.Tests.Occurrence.RootCatalog.Baseline
import LeanInformationAudit.Tests.Occurrence.RootCatalog.Contributor

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.RootCatalog

run_cmd RootCatalogs.declare { designatedContract with source := causalRows }

-- Use the same finite causal seal limits as SharedInformationRoot.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#seal_information_theory

-- Real separately compiled contributors supply the positive control. Native
-- declaration ownership cannot be established by setMainModule simulation.
run_cmd do
  let env ← getEnv
  validateRegistrySnapshot env
  let actual := SealRecords.occurrencesForRoot env designatedRoot
  unless actual.size == 3 && SealRecords.systemCatalogIrredundant env designatedRoot do
    throwError "fixture designated root lost an occurrence or irredundancy proof"
  let causal := actual.filter (·.registrationModuleName == causalContributor)
  unless causal.size == 2 && causal.all (fun row =>
      row.catalogId == `fixtureCausal && row.objectArenaName == causalRows[0]!.objectArenaName) do
    throwError "fixture causal contributor/catalog identity mismatch"
  for row in InformationRegistry.entries env do
    unless (env.getModuleIdxFor? row.unitName).map (env.header.moduleNames[·.toNat]!) ==
        some row.registrationModuleName do
      throwError "fixture registration unit has the wrong native contributor"
  for record in SealRecords.forRoot env designatedRoot do
    let some (.thmInfo _) := env.find? record.verdict.name
      | throwError "fixture irredundancy certificate is not a theorem"
    elabCommand (← `(command| #print axioms $(mkIdent record.verdict.name)))
  logInfo "fixture designated seal: actual=expected=3; two native contributors; irredundant"
