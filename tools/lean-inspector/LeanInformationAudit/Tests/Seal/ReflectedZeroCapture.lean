import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralCatalog
import LeanInformationAudit.Tests.Seal.ZeroMessage
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Seal.ReflectedZeroCapture

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

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def __state_enumeration : Arena.StateEnumeration arena.toArena where
  states := [false, true]
  nodup := by decide
  complete := by decide

end arena

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def testRealization : PrimitiveRealization arena.signature where
  readout := fun _ _ => false
  anchor := Fin.elim0

test_assess in information_theorem target
  in arena
  primitives testRealization
  : arena.Law testRealization := by trivial

test_assess in expect_information_occurrence target
  in arena
  from "LeanInformationAudit.Tests.Seal.ReflectedZeroCapture"

run_cmd do
  let before := (← get).messages
  LeanInformationAudit.prepareSealPublication (← validateSourceSnapshot (← Lean.getEnv).header.mainModule (InformationRegistry.entries (← Lean.getEnv)))
  LeanInformationAudit.Tests.checkZeroMessages "finite" 1 before

end LeanInformationAudit.Tests.Seal.ReflectedZeroCapture
