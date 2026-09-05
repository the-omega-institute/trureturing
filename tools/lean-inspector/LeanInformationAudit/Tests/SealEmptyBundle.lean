import LeanInformationAudit.SealCommand

open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealEmptyBundle

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature :=
    { Index := Fin 0
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun index => index.elim0
      readoutAxisNotAnchor := fun index => index.elim0
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def fixtureRealization : PrimitiveRealization arena.signature where
  readout := fun index => index.elim0
  anchor := fun index => index.elim0

information_theorem theoremWithoutPrimitives
  in arena
  primitives fixtureRealization
  : arena.Law fixtureRealization := by trivial

/-- error: IE-C013 MissingPrimitiveBundle:
LeanInformationAudit.Tests.SealEmptyBundle.theoremWithoutPrimitives -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.SealEmptyBundle
