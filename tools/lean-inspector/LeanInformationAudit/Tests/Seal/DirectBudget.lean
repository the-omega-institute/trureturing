import LeanInformationAudit.SealCommand

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Seal.DirectBudget

set_option linter.style.longLine false

def objectArena : Arena := Arena.ofFintype (Fin 257)

def lawArena : PrimitiveLawArena where
  toArena := objectArena
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Fin 257
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

information_theorem target
  in lawArena
  object_arena objectArena
  catalog oversized
  primitives fixtureRealization
  : lawArena.Law fixtureRealization := by trivial

set_option maxRecDepth 100000 in
/-- error: IE-C032 SizeBudgetRequiresReflectedSeal root=LeanInformationAudit.Tests.Seal.DirectBudget catalog=oversized pair_budget=65792 limit=65536 seal=LeanInformationAudit.Tests.Seal.DirectBudget -/
#guard_msgs (error) in
#seal_information_theory

#print axioms
  target.«LeanInformationAudit.Tests.Seal.DirectBudget/LeanInformationAudit.Tests.Seal.DirectBudget.objectArena/oversized».__primitive_realization
#print axioms
  target.«LeanInformationAudit.Tests.Seal.DirectBudget/LeanInformationAudit.Tests.Seal.DirectBudget.objectArena/oversized».__information_unit

end LeanInformationAudit.Tests.Seal.DirectBudget
