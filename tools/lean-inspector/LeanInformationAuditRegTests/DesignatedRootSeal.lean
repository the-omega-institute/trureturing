import Reg.Catalogs.SharedInformationRoot.SealedCatalog
import Reg.Catalogs.InformationRoot.SealedCatalog
import LeanInformationAuditRegTests.ProductionInputs
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Lean.Elab.Command LeanInformationAudit
open Reg.Support

-- Inspect the complete seal published by the real registration owners.
-- Report companions preserve each original registration owner.
run_cmd do
  let env ← getEnv
  let root := `Reg.Catalogs.SharedInformationRoot.SealedCatalog
  if (SealRecords.analysisForRoot? env root).isSome ||
      env.contains (root.str "__system_catalog_irredundant") then
    throwError "DesignatedRootSeal closure contains analysis staging"
  let actual := SealRecords.occurrencesForRoot env root
  let some catalog := RootCatalogs.find? env root
    | throwError "ROOT-B-designated-seal: missing typed root catalog"
  let expected := catalog.expected
  unless actual.size == 13 && expected.size == 13 do
    throwError "ROOT-B-designated-seal: expected actual=expected=13"
  -- Preserve the production 11/13 source split alongside the generic split test.
  let some frozenCatalog := RootCatalogs.find? env `Reg.Catalogs.InformationRoot.SealedCatalog
    | throwError "ROOT-B-snapshot-split: missing typed information catalog"
  let frozen := frozenCatalog.expected
  let sameOccurrence (left right : SnapshotOccurrence) : Bool :=
    left.theoremName == right.theoremName && left.objectArenaName == right.objectArenaName &&
    left.registrationModuleName == right.registrationModuleName &&
    left.statementIdentity == right.statementIdentity
  unless frozen.size == 11 && frozen.all (fun row => expected.any (sameOccurrence row)) do
    throwError "ROOT-B-snapshot-split: production frozen contributor inventory changed"
  let sourceCausal := expected.filter fun row =>
    row.objectArenaName == `Reg.Support.LegacyCausalCoordinates.objectArena &&
    #[`D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention].contains row.theoremName
  unless sourceCausal.size == 2 && sourceCausal.all (fun row =>
      row.objectArenaName ==
        `Reg.Support.LegacyCausalCoordinates.objectArena &&
      expected.any (sameOccurrence row) && !frozen.any (sameOccurrence row)) do
    throwError "ROOT-B-snapshot-split: production causal source inventory changed"
  let causal := actual.filter fun row => sourceCausal.any fun source =>
    row.registrationModuleName == source.registrationModuleName &&
    row.theoremName == source.theoremName && row.objectArenaName == source.objectArenaName
  let causalArena :=
    `Reg.Support.LegacyCausalCoordinates.objectArena
  unless causal.size == 2 && causal.all (fun row =>
      row.catalogId == `«causal-unified-transitions» && row.objectArenaName == causalArena) do
    throwError "ROOT-B-designated-seal: causal contributor/catalog identity mismatch"
  discard <| liftCoreM <| LeanInformationAuditRegTests.productionEntries expected
  let records := SealRecords.forRoot env root
  unless records.size == 12 do throwError "ROOT-B-designated-seal: expected twelve catalogs"
  let artifact ← liftTermElabM <| serializeSealArtifact records
  let expectedSealDigest := "3b969421f5726c72b71662d11b77978b056189af10609ec303fcca1a0aac2d45"
  unless Sha256.hex artifact.toUTF8 == expectedSealDigest do
    throwError "ROOT-B-designated-seal: independent digest mismatch; expected={expectedSealDigest}; actual={Sha256.hex artifact.toUTF8}"
  unless SealRecords.systemCatalogIrredundant env root do
    throwError "ROOT-B-designated-seal: system_catalog_irredundant lacks staged proofs"
  for record in records do
    let some (.thmInfo _) := env.find? record.verdict.name
      | throwError "ROOT-B-designated-seal: irredundancy certificate is not a theorem"
    elabCommand (← `(command| #print axioms $(mkIdent record.verdict.name)))
  logInfo "ROOT-B-designated-seal: actual=expected=13 system_catalog_irredundant=true"
