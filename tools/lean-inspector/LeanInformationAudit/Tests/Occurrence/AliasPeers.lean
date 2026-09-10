import LeanInformationAudit.SealCommand
open Lean
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
namespace AliasPeers
def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool)
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
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def fstRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.1
  anchor := Fin.elim0

def sndRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.2
  anchor := Fin.elim0

information_theorem fstTheorem
  in arena
  primitives fstRealization
  : arena.Law fstRealization := by trivial

def cloneArena := arena
abbrev abbreviatedArena := cloneArena
@[reducible] def chainedArena := id abbreviatedArena
local instance : DecidableEq chainedArena.State := chainedArena.toArena.stateDecidableEq

information_theorem sndTheorem
  in chainedArena
  primitives sndRealization
  : arena.Law sndRealization := by trivial

expect_information_occurrence fstTheorem in arena
  from "LeanInformationAudit.Tests.Occurrence.AliasPeers"
expect_information_occurrence sndTheorem in chainedArena
  from "LeanInformationAudit.Tests.Occurrence.AliasPeers"
run_cmd do
  let some entry := InformationRegistry.find? (← getEnv) `AliasPeers.sndTheorem
    | throwError "missing alias registration"
  unless entry.arenaName == `AliasPeers.chainedArena &&
      entry.canonicalObjectArenaName == `AliasPeers.arena do
    throwError "AliasPeers: registration must retain spelling and resolved owner"
#seal_information_theory
run_cmd do
  let records := SealRecords.forRoot (← getEnv) (← getEnv).header.mainModule
  let [record] := records.toList
    | throwError "AliasPeers: expected one catalog"
  unless record.catalog.arenaName == `AliasPeers.arena &&
      record.theorems.map (·.uniqueCaptureCount) == #[4, 4] do
    throwError "AliasPeers: expected one catalog with two positive peers"
#print axioms arena.__catalog_irredundant
end AliasPeers
