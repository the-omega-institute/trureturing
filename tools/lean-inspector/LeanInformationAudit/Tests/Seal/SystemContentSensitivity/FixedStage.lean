import LeanInformationAudit.SealCommand

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.Seal.T013FixedStage

private abbrev censusArena : Arena := Arena.ofFintype Bool

private abbrev censusBundle (stage : Bool) : PrimitiveBundle Bool where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ =>
    { axis := .cut
      kernel := cutKernel fun state => if stage then state else false }

private abbrev censusUnit (stage : Bool) : TheoremUnit censusArena := by
  exact ⟨censusBundle stage, True, True.intro⟩

private abbrev censusCatalog (stage : Bool) : Catalog censusArena :=
  { Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    theoremAt := fun _ => censusUnit stage }

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

def fixedStageRealization : PrimitiveRealization arena.signature where
  readout := fun _ _ => (censusCatalog false).uniqueCaptureCount (0 : Fin 1)
  anchor := Fin.elim0

information_theorem systemTheorem
  in arena
  primitives fixedStageRealization
  : arena.Law fixedStageRealization := by trivial

/-- error: IE-C007 ZeroUniqueCapture: theorem
LeanInformationAudit.Tests.Seal.T013FixedStage.systemTheorem arena
LeanInformationAudit.Tests.Seal.T013FixedStage.arena full 2 without 2 -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.Seal.T013FixedStage
