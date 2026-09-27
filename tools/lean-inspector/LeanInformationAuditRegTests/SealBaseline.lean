import Reg.Catalogs.InformationRoot
import LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership

open Lean
open LeanInformationAudit
open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscape.SystemUnit

namespace LeanInformationAudit.Tests.SealBaseline

set_option maxRecDepth 100000

run_cmd do
  let records := SealRecords.forRoot (← getEnv) Reg.Support.InformationRootContract.rootId
  let artifact ← Lean.Elab.Command.liftTermElabM <| serializeSealArtifact records
  let digest := Sha256.hex artifact.toUTF8
  -- Persisted InformationRoot records under the role-named seal schema.
  unless digest == Reg.Support.InformationRootContract.expectedSealDigest do
    throwError "seal artifact digest mismatch: {digest}"

example : D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena».__information_catalog.uniqueCaptureCount (0 : Fin 1) = 570 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena».__information_catalog.uniqueCaptureCount (0 : Fin 1) = 12 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena».__information_catalog.uniqueCaptureCount (0 : Fin 1) = 20 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena».__information_catalog.uniqueCaptureCount (0 : Fin 1) = 56 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena».__information_catalog.uniqueCaptureCount (0 : Fin 1) = 240 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena/D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena».__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 968 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena/D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena».__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 6 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena/D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena».__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 12 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena/D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena».__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 48 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena/D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena».__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 60 := by
  decide

example : D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena/D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena».__information_catalog.uniqueCaptureCount (0 : Fin 1) = 2 := by
  decide

#check D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena».__lowers_escape
#check D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena».__catalog_irredundant
#print axioms D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena.«Reg.Catalogs.InformationRoot/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena».__catalog_irredundant


run_meta do
  let env ← getEnv
  let root := Reg.Support.InformationRootContract.rootId
  let expected := Reg.Support.InformationRootContract.contract.expected
  let records := SealRecords.forRoot env root
  let actual := SealRecords.occurrencesForRoot env root
  unless expected.size == 11 && actual.size == 11 && records.size == 11 do
    throwError "expected eleven production catalogs and occurrences"
  let raw := InformationRegistry.entries env
  unless raw.size == 11 do throwError "resealing changed registration occurrence count"
  for row in expected do
    let matchedRows := raw.filter fun entry => entry.theoremName == row.theoremName &&
      entry.canonicalObjectArenaName == row.objectArenaName &&
      entry.registrationModuleName == row.registrationModuleName &&
      entry.statementIdentity == row.statementIdentity
    unless matchedRows.size == 1 do throwError "production expectation not uniquely realized"
  for record in records do
    for name in #[record.catalog.catalogName, record.verdict.name] ++
        record.theorems.flatMap (fun row => #[row.unitName, row.realizationName,
          row.certificateName]) do
      let some index := env.getModuleIdxFor? name | throwError "missing compiler owner: {name}"
      unless env.header.moduleNames[index.toNat]! == root do
        throwError "companion has wrong compiler owner: {name}"
  let owners := (expected.map (·.registrationModuleName)).toList.eraseDups
  for owner in owners do
    let count := (expected.filter (·.registrationModuleName == owner)).size
    LeanInformationAudit.Tests.Occurrence.RootCatalog.Ownership.checkImportedOwners owner count
  let bindings := TemplateBinding.records env
  for row in expected do
    let some observed := bindings.find? fun entry =>
        entry.occurrence.key.theoremName == row.theoremName &&
        entry.occurrence.key.registrationModule == row.registrationModuleName
      | throwError "missing production binding row"
    unless observed.result matches .undeclared do throwError "production status changed"
  logInfo "[PASS] Reg root: 11 catalogs, 11 occurrences, 55 native companions, 11 undeclared statuses"

end LeanInformationAudit.Tests.SealBaseline
