import LeanInformationAudit.SealCommand
open Lean
open D5.S3.ConceptDynamics.InformationEscape
namespace P2CloneSplit
def arena : PrimitiveLawArena.{0,0,0} where
  toArena := Arena.ofFintype Bool
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => (1 + 1 : Nat) = 2
local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
def readouts : PrimitiveRealization arena.signature where
  readout := fun _ x => x
  anchor := Fin.elim0
theorem first : (1 + 1 : Nat) = 2 := by decide
theorem second : (1 + 1 : Nat) = 2 := by decide
theorem bridge : LegacyPrimitiveRealization arena ((1 + 1 : Nat) = 2) readouts where
  equivalence := Iff.rfl
register_information_theorem first in arena primitives readouts.toPrimitiveBundle realization bridge
def cloneArena := arena
theorem bridgeSecond : LegacyPrimitiveRealization cloneArena ((1 + 1 : Nat) = 2) readouts where
  equivalence := Iff.rfl
register_information_theorem second in cloneArena primitives readouts.toPrimitiveBundle realization bridgeSecond
def cat : Catalog arena.toArena := Catalog.ofVector ![first.__information_unit,second.__information_unit]
example : cat.uniqueCaptureCount (0 : Fin 2) = 0 := by decide
example : cat.uniqueCaptureCount (1 : Fin 2) = 0 := by decide
expect_information_occurrence first in arena from "LeanInformationAudit.Tests.Occurrence.P2CloneSplit"
expect_information_occurrence second in cloneArena from "LeanInformationAudit.Tests.Occurrence.P2CloneSplit"
run_cmd do
  let catalogs ← LeanInformationAudit.prepareCatalogs
  let [prepared] := catalogs.toList
    | throwError "P2CloneSplit: aliases split the maximal catalog"
  unless prepared.record.units.size == 2 &&
      prepared.record.arenaName == `P2CloneSplit.arena &&
      prepared.record.catalogId == `P2CloneSplit.arena do
    throwError "P2CloneSplit: aliases split the maximal catalog"

#guard_msgs (error) in
#seal_information_theory

run_cmd do
  let env ← getEnv
  unless (LeanInformationAudit.SealRecords.forRoot env env.header.mainModule).size == 1 do
    throwError "P2CloneSplit: missing classification seal"
end P2CloneSplit
