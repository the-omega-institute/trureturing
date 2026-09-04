import LeanInformationAudit.SealCommand

/-! This negative fixture is isolated because registry entries persist through imports. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealCollision

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

def notFstRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => !state.1
  anchor := Fin.elim0

information_theorem fstTheorem
  in arena
  primitives fstRealization
  : arena.Law fstRealization := by trivial

information_theorem notFstTheorem
  in arena
  primitives notFstRealization
  : arena.Law notFstRealization := by trivial

/-- error: IE-C007 ZeroUniqueCapture: theorem
LeanInformationAudit.Tests.SealCollision.fstTheorem arena
LeanInformationAudit.Tests.SealCollision.arena full 4 without 4 -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.SealCollision
