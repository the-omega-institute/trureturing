import LeanInformationAudit.SealCommand

/-! Positive seal fixtures stay in this test module so their persistent registry
entries are never imported by a production root. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealSuccess

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

information_theorem sndTheorem
  in arena
  primitives sndRealization
  : arena.Law sndRealization := by trivial

#seal_information_theory

#check fstTheorem.__lowers_escape
#check sndTheorem.__escape_enriched
#check arena.__information_catalog
#check arena.__catalog_irredundant

end LeanInformationAudit.Tests.SealSuccess
