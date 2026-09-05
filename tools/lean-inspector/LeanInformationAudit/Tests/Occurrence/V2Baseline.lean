import D5.S3.ConceptDynamics.InformationEscape.InformationRoot

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

namespace LeanInformationAudit.Tests.V2Baseline

set_option maxRecDepth 100000

run_cmd do
  let records := SealRecords.forRoot (← getEnv) frozenInformationRootId
  let artifact := serializeV2Artifact records
  let digest := Sha256.hex artifact.toUTF8
  -- Produced once from these persisted InformationRoot records with origin/dev's
  -- byte-identical production serializer; the frozen root itself was not modified.
  unless digest == "6da462e5cbfa01261eb820dd4c236f647632fd36fe8df9a391ec5ed9800cd16b" do
    throwError "v2 artifact digest mismatch: {digest}"

example : agendaPowerArena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 570 := by
  decide

example : residueArena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 12 := by
  decide

example : spectrumArena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 20 := by
  decide

example : contextArena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 56 := by
  decide

example : interventionArena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 240 := by
  decide

example : observationInterventionArena.__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 968 := by
  decide

example : staticExactExperimentArena.__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 6 := by
  decide

example : commutingCompletionArena.__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 12 := by
  decide

example : localLawGluingArena.__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 48 := by
  decide

example : endStateOmitsPreemptingCauseArena.__information_catalog.uniqueCaptureCount
    (0 : Fin 1) = 60 := by
  decide

example : arena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 2 := by
  decide

#check agenda_power.__lowers_escape
#check agendaPowerArena.__catalog_irredundant
#print axioms agenda_power.__lowers_escape
#print axioms agendaPowerArena.__catalog_irredundant

end LeanInformationAudit.Tests.V2Baseline
