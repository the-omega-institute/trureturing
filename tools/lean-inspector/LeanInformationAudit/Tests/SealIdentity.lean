import LeanInformationAudit.SealCommand

/-! T-006: one product-valued identity readout captures all 12 ordered
off-diagonal pairs in the four-state arena. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealIdentity

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool)
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool × Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def idRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

information_theorem idTheorem
  in arena
  primitives idRealization
  : arena.Law idRealization := by trivial

#seal_information_theory

example :
    arena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 12 := by
  decide

#check idTheorem.__lowers_escape

#print axioms idTheorem.__lowers_escape

end LeanInformationAudit.Tests.SealIdentity
