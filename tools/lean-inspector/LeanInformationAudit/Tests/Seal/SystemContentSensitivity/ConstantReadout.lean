import LeanInformationAudit.SealCommand

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Seal.T013Constant

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Nat
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def constantRealization : PrimitiveRealization arena.signature where
  readout := fun _ _ => (0 : Nat)
  anchor := Fin.elim0

information_theorem systemTheorem
  in arena
  primitives constantRealization
  : arena.Law constantRealization := by trivial

private def fixtureCatalog : Catalog arena.toArena :=
  Catalog.ofVector ![systemTheorem.__information_unit]

example : fixtureCatalog.uniqueCaptureCount (0 : Fin 1) = 0 := by decide

/-- error: IE-C007 ZeroUniqueCapture: theorem
LeanInformationAudit.Tests.Seal.T013Constant.systemTheorem arena
LeanInformationAudit.Tests.Seal.T013Constant.arena full 2 without 2 -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.Seal.T013Constant
