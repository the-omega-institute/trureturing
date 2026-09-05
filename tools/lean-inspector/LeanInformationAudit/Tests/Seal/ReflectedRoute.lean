import LeanInformationAudit.SealCommand
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations

open Lean
open Lean.Meta
open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations

namespace LeanInformationAudit.Tests.Seal.ReflectedRoute

set_option maxRecDepth 100000

register_information_theorem
  agenda_power
  in agendaPowerArena
  primitives agendaPowerRealization.toPrimitiveBundle
  realization agenda_power_realization

expect_information_occurrence agenda_power
  in agendaPowerArena
  from "LeanInformationAudit.Tests.Seal.ReflectedRoute"

/-- info: information seal: arena=D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena theorem=D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power unique=570 method=reflected-fused-counts -/
#guard_msgs (info) in
#seal_information_theory

/- Mutation pin: corrupting a reflected role bin at the snapshot boundary makes the
guarded seal above fail with IE-C009 `role histogram mismatch`. -/

/-- info: reflected transport: agenda_power.__lowers_escape references Catalog.uniqueCaptureCount_pos_of_fused -/
#guard_msgs (info) in
run_cmd do
  let proofName :=
    `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power.__lowers_escape
  let info ← getConstInfo proofName
  let some value := info.value? (allowOpaque := true)
    | throwError "generated reflected lowering theorem has no proof value"
  unless value.containsConst
      (· == `D5.S3.ConceptDynamics.InformationEscape.Catalog.uniqueCaptureCount_pos_of_fused) do
    throwError
      "generated reflected lowering theorem does not reference \
Catalog.uniqueCaptureCount_pos_of_fused"
  logInfo
    "reflected transport: agenda_power.__lowers_escape references \
Catalog.uniqueCaptureCount_pos_of_fused"

end LeanInformationAudit.Tests.Seal.ReflectedRoute
