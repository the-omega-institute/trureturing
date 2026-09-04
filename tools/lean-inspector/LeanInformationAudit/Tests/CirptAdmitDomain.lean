import D5.S3.ConceptDynamics.CIRPT.SemanticIntegrity
import LeanInformationAudit.SealCommand

/-! T-CIRPT-003 / IE-C017: ADMIT cannot narrow the audited pair domain. -/

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.CirptAdmitDomain

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
local instance : Fintype arena.State := arena.toArena.stateFintype

def registeredRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.1
  anchor := Fin.elim0

information_theorem registeredTheorem
  in arena
  primitives registeredRealization
  : arena.Law registeredRealization := by trivial

def admit (state : arena.State) : Prop := state.2 = true

local instance : DecidablePred admit := by
  intro state
  unfold admit
  infer_instance

example :
    admitKernel admit = cutKernel (fun state => decide (admit state)) := by
  exact full_domain_admit_encoding admit

example :
    forall pair, pair ∈ offDiagonalPairs arena.State ->
      (bundleWithAtom registeredTheorem.__information_unit.primitives
        { axis := .admit, kernel := admitKernel admit }).agrees pair.1 pair.2 ->
      registeredTheorem.__information_unit.primitives.agrees pair.1 pair.2 := by
  exact admit_atom_preserves_offDiagonalPairs
    registeredTheorem.__information_unit.primitives admit

example (x y : arena.State) :
    (bundleWithAtom registeredTheorem.__information_unit.primitives
      { axis := .admit, kernel := admitKernel admit }).agrees x y ->
    registeredTheorem.__information_unit.primitives.agrees x y := by
  exact adding_admit_atom_cannot_increase_agreement
    registeredTheorem.__information_unit.primitives admit x y

end LeanInformationAudit.Tests.CirptAdmitDomain
