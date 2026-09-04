import LeanInformationAudit.SealCommand

/-! Positive seal fixtures stay in this test module so their persistent registry
entries are never imported by a production root. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealSuccess

/-! T-003/T-007: the two projections each uniquely capture one coordinate. -/

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

universe u

def polymorphicArena (X : Type u) [Fintype X] [DecidableEq X] :
    PrimitiveLawArena where
  toArena := Arena.ofFintype X
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

/-! T-001: instantiate a universe-polymorphic arena and use a non-identity Bool CUT. -/
def t001Arena := polymorphicArena Bool

local instance : DecidableEq t001Arena.State :=
  t001Arena.toArena.stateDecidableEq

def notRealization : PrimitiveRealization t001Arena.signature where
  readout := fun _ state => !state
  anchor := Fin.elim0

information_theorem notTheorem
  in t001Arena
  primitives notRealization
  : t001Arena.Law notRealization := by trivial

#seal_information_theory

#check fstTheorem.__lowers_escape
#check sndTheorem.__escape_enriched
#check arena.__information_catalog
#check arena.__catalog_irredundant
#check notTheorem.__lowers_escape
#check t001Arena.__catalog_irredundant

#print axioms fstTheorem.__lowers_escape
#print axioms fstTheorem.__escape_enriched
#print axioms sndTheorem.__lowers_escape
#print axioms sndTheorem.__escape_enriched
#print axioms arena.__catalog_irredundant
#print axioms notTheorem.__lowers_escape
#print axioms notTheorem.__escape_enriched
#print axioms t001Arena.__catalog_irredundant

end LeanInformationAudit.Tests.SealSuccess
