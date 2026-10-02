import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

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

test_assess in information_theorem systemTheorem
  in arena
  primitives constantRealization
  : arena.Law constantRealization := by trivial

private def fixtureCatalog : Catalog arena.toArena :=
  Catalog.ofVector ![systemTheorem.__information_unit]

example : fixtureCatalog.uniqueCaptureCount (0 : Fin 1) = 0 := by decide

test_assess in expect_information_occurrence systemTheorem
  in arena
  from "LeanInformationAudit.Tests.Seal.SystemContentSensitivity.ConstantReadout"

#guard_msgs (error) in
test_assess in #seal_information_theory

end LeanInformationAudit.Tests.Seal.T013Constant
