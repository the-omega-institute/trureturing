import LeanInformationAudit.SealCommand

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Seal.IllTypedEnumeration

def arena : PrimitiveLawArena where
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
  Law := fun _ => True

namespace arena

def __state_enumeration : Nat := 2

end arena


local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def testRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

information_theorem target
  in arena
  primitives testRealization
  : arena.Law testRealization := by trivial

/-- error: IE-C009 ProofConstructionFailed: LeanInformationAudit.Tests.Seal.IllTypedEnumeration.arena.__state_enumeration
expected type Arena.StateEnumeration LeanInformationAudit.Tests.Seal.IllTypedEnumeration.arena.toArena -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.Seal.IllTypedEnumeration
