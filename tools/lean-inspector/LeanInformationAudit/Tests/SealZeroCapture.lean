import LeanInformationAudit.SealCommand

/-! This negative fixture is isolated because registry entries persist through imports. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealZeroCapture

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

def realization : PrimitiveRealization arena.signature where
  readout := fun _ _ => false
  anchor := Fin.elim0

information_theorem constantTheorem
  in arena
  primitives realization
  : arena.Law realization := by trivial

/-- error: IE-C007 ZeroUniqueCapture: theorem
LeanInformationAudit.Tests.SealZeroCapture.constantTheorem arena
LeanInformationAudit.Tests.SealZeroCapture.arena full 12 without 12 -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.SealZeroCapture
