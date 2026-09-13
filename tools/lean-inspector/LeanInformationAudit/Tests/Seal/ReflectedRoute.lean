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

open D5.S3.ConceptDynamics.InformationEscape

def localArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := {
    Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    Output := fun _ => Bool
    outputDecidableEq := fun _ => inferInstance
    axis := fun _ => .cut
    readoutAxisNotAnchor := by simp
    AnchorIndex := Fin 0
    anchorFintype := inferInstance
    anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq localArena.State := localArena.toArena.stateDecidableEq

def localRealization : PrimitiveRealization localArena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

information_theorem localTheorem in localArena primitives localRealization
  : localArena.Law localRealization := by trivial

expect_information_occurrence localTheorem in localArena
  from "LeanInformationAudit.Tests.Seal.ReflectedRoute"

/--
info: information seal: arena=LeanInformationAudit.Tests.Seal.ReflectedRoute.localArena theorem=LeanInformationAudit.Tests.Seal.ReflectedRoute.localTheorem unique=2 method=decide
---
info: information seal: arena=D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena theorem=D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power unique=570 method=reflected-fused-counts
-/
#guard_msgs (info) in
#seal_information_theory

-- Ordinary same-module resolution must remain usable for every family.
example : agenda_power.__information_unit = agenda_power.__information_unit := rfl
example : agendaPowerArena.__information_catalog = agendaPowerArena.__information_catalog := rfl
example : agenda_power.__lowers_escape = agenda_power.__lowers_escape := rfl
example : agenda_power.__escape_enriched = agenda_power.__escape_enriched := rfl
example : agendaPowerArena.__catalog_irredundant = agendaPowerArena.__catalog_irredundant := rfl
example : localTheorem.__information_unit = localTheorem.__information_unit := rfl
example : localArena.__information_catalog = localArena.__information_catalog := rfl
example : localTheorem.__lowers_escape = localTheorem.__lowers_escape := rfl
example : localTheorem.__escape_enriched = localTheorem.__escape_enriched := rfl
example : localArena.__catalog_irredundant = localArena.__catalog_irredundant := rfl

/- Mutation pin: corrupting a reflected role bin at the snapshot boundary makes the
guarded seal above fail with IE-C009 `role histogram mismatch`. -/

/-- info: reflected transport: agenda_power.__lowers_escape references Catalog.uniqueCaptureCount_pos_of_fused -/
#guard_msgs (info) in
run_cmd do
  let proofName := ``agenda_power.__lowers_escape
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
