import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Seal.DecideRoute

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

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def testRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

test_assess in information_theorem target
  in arena
  primitives testRealization
  : arena.Law testRealization := by trivial

test_assess in expect_information_occurrence target
  in arena
  from "LeanInformationAudit.Tests.Seal.DecideRoute"

/-- info: information seal: arena=LeanInformationAudit.Tests.Seal.DecideRoute.arena theorem=LeanInformationAudit.Tests.Seal.DecideRoute.target unique=2 method=decide -/
#guard_msgs (info) in
test_assess in #seal_information_theory

end LeanInformationAudit.Tests.Seal.DecideRoute
