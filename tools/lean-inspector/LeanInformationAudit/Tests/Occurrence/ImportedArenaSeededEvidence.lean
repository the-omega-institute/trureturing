import LeanInformationAudit.Tests.Occurrence.DesignatedRootSeal

open Lean Elab Command LeanInformationAudit

-- SharedInformationRoot seals without registering or declaring a contract.
-- Its native contributors must already carry every retained seed's input evidence.
run_cmd do
  for contract in currentRootCatalogContracts do
    for rows in #[contract.expected, contract.source, contract.baseline] do
      for row in rows do
        unless (← getEnv).contains row.objectArenaName do
          throwError "production seed is not loaded: {row.objectArenaName}"
        discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence row.objectArenaName
  logInfo "both production contracts retain expected/source/baseline compiled provenance"
