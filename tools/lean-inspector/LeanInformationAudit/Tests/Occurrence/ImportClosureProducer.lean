import LeanInformationAudit.Syntax

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.ImportClosureProducer

set_option linter.style.longLine false

def objectArena : Arena := Arena.ofFintype Bool

def lawArena : PrimitiveLawArena where
  toArena := objectArena
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

local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq

def fixtureRealization : PrimitiveRealization lawArena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

information_theorem importedTheorem
  in lawArena
  object_arena objectArena
  catalog importedBool
  primitives fixtureRealization
  : lawArena.Law fixtureRealization := by trivial

#print axioms
  importedTheorem.«LeanInformationAudit.Tests.Occurrence.ImportClosureProducer/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__primitive_realization
#print axioms
  importedTheorem.«LeanInformationAudit.Tests.Occurrence.ImportClosureProducer/LeanInformationAudit.Tests.ImportClosureProducer.objectArena/importedBool».__information_unit

end LeanInformationAudit.Tests.ImportClosureProducer
