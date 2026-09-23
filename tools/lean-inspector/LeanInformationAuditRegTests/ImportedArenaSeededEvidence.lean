import LeanInformationAuditRegTests.DesignatedRootSeal

open Lean Elab Command LeanInformationAudit

-- The downstream production closure must retain every existing seed's
-- expected/source/baseline evidence through ordinary compiler imports.
run_cmd do
  for contract in currentRootCatalogContracts do
    for rows in #[contract.expected, contract.source, contract.baseline] do
      for row in rows do
        unless (← getEnv).contains row.objectArenaName do
          throwError "production seed is not loaded: {row.objectArenaName}"
        discard <| liftTermElabM <| resolveCanonicalArenaNameFromEvidence row.objectArenaName
  logInfo "both production contracts retain expected/source/baseline compiled provenance"
