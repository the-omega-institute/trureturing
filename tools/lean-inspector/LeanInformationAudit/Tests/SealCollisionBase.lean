import LeanInformationAudit.Syntax

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealCollisionFixture

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

def fixtureRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.1
  anchor := Fin.elim0

theorem target : arena.Law fixtureRealization := by trivial

def persistedUnit : TheoremUnit arena.toArena :=
  { «primitives» := fixtureRealization.toPrimitiveBundle
    Statement := arena.Law fixtureRealization
    proof := target }

end LeanInformationAudit.Tests.SealCollisionFixture
