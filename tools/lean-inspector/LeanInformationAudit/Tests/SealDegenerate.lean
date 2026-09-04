import LeanInformationAudit.SealCommand

/-! This negative fixture is isolated because registry entries persist through imports. -/

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealDegenerate

def arena : PrimitiveLawArena.{0, 0, 0} where
  toArena := Arena.ofFintype PUnit
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => PUnit
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def unitRealization : PrimitiveRealization arena.signature where
  readout := fun _ _ => PUnit.unit
  anchor := Fin.elim0

information_theorem degenerateTheorem
  in arena
  primitives unitRealization
  : arena.Law unitRealization := by trivial

/-- error: IE-C004 DegenerateArena:
LeanInformationAudit.Tests.SealDegenerate.arena -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.SealDegenerate
