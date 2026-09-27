import Reg.Catalogs.SharedInformationRoot
import LeanInformationAuditRegTests.ProductionInputs

open Lean Lean.Elab.Command LeanInformationAudit
open Reg.Support

-- Inspect the complete seal published by the real registration owners.
-- Simulating another mainModule cannot supply native occurrence ownership.
run_cmd do
  let env ← getEnv
  let root := SharedInformationRootContract.rootId
  if (SealRecords.analysisForRoot? env root).isSome ||
      env.contains (root.str "__system_catalog_irredundant") then
    throwError "DesignatedRootSeal closure contains analysis staging"
  let actual := SealRecords.occurrencesForRoot env root
  let expected := SharedInformationRootContract.contract.expected
  unless actual.size == 13 && expected.size == 13 do
    throwError "ROOT-B-designated-seal: expected actual=expected=13"
  -- Preserve the production 11/13 source split alongside the generic split test.
  let frozen := InformationRootContract.contract.expected
  let sameOccurrence (left right : SnapshotOccurrence) : Bool :=
    left.theoremName == right.theoremName && left.objectArenaName == right.objectArenaName &&
    left.registrationModuleName == right.registrationModuleName &&
    left.statementIdentity == right.statementIdentity
  unless frozen.size == 11 && frozen.all (fun row => expected.any (sameOccurrence row)) do
    throwError "ROOT-B-snapshot-split: production frozen contributor inventory changed"
  let sourceCausal := SharedInformationRootContract.causalOccurrences
  unless sourceCausal.size == 2 && sourceCausal.all (fun row =>
      row.objectArenaName ==
        `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena &&
      expected.any (sameOccurrence row) && !frozen.any (sameOccurrence row)) do
    throwError "ROOT-B-snapshot-split: production causal source inventory changed"
  let causal := actual.filter fun row => sourceCausal.any fun source =>
    row.registrationModuleName == source.registrationModuleName &&
    row.theoremName == source.theoremName && row.objectArenaName == source.objectArenaName
  let causalArena :=
    `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena
  unless causal.size == 2 && causal.all (fun row =>
      row.catalogId == `«causal-unified-transitions» && row.objectArenaName == causalArena) do
    throwError "ROOT-B-designated-seal: causal contributor/catalog identity mismatch"
  discard <| liftCoreM <| LeanInformationAuditRegTests.productionEntries expected
  let records := SealRecords.forRoot env root
  unless records.size == 12 do throwError "ROOT-B-designated-seal: expected twelve catalogs"
  let artifact ← liftTermElabM <| serializeSealArtifact records
  unless Sha256.hex artifact.toUTF8 == SharedInformationRootContract.expectedSealDigest do
    throwError "ROOT-B-designated-seal: independent digest mismatch"
  unless SealRecords.systemCatalogIrredundant env root do
    throwError "ROOT-B-designated-seal: system_catalog_irredundant lacks staged proofs"
  for record in records do
    let some (.thmInfo _) := env.find? record.verdict.name
      | throwError "ROOT-B-designated-seal: irredundancy certificate is not a theorem"
    elabCommand (← `(command| #print axioms $(mkIdent record.verdict.name)))
  logInfo "ROOT-B-designated-seal: actual=expected=13 system_catalog_irredundant=true"
