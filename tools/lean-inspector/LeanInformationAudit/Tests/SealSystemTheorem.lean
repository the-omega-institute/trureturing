import LeanInformationAudit.SealCommand

/-! T-013: a stage readout computes the engine's own leave-one-out census.

The seal consumes only primitive kernels (`CatalogBuilder.lean:50-53`), not `Law`.
A direct `Law := True` mutation is therefore caught by the literal statement-shape
check, not by the seal. -/

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.SealSystemTheorem

private abbrev censusArena : Arena := Arena.ofFintype Bool

private abbrev censusBundle (stage : Bool) : PrimitiveBundle.{0, 0} Bool where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ =>
    { axis := .cut
      kernel := cutKernel fun state => if stage then state else false }

private abbrev censusUnit (stage : Bool) : TheoremUnit.{0, 0} censusArena := by
  exact ⟨censusBundle stage, True, True.intro⟩

abbrev censusCatalog (stage : Bool) : Catalog.{0, 0, 0} censusArena :=
  { Index := Fin 1
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    theoremAt := fun _ => censusUnit stage }

abbrev systemReadout (stage : Bool) : Nat :=
  (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)

abbrev SystemCharacterization : Prop :=
  ∀ stage : Bool,
    (censusCatalog stage).LowersEscape (0 : Fin 1) ↔
      0 < (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)

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
  Law := fun candidate =>
    (∀ stage, candidate.readout 0 stage = systemReadout stage) ∧
      SystemCharacterization

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def systemRealization : PrimitiveRealization arena.signature where
  readout := fun (_ : Fin 1) (stage : Bool) => systemReadout stage
  anchor := Fin.elim0

information_theorem systemTheorem
  in arena
  primitives systemRealization
  : arena.Law systemRealization := by
    constructor
    · intro stage
      rfl
    intro stage
    exact Catalog.lowersEscape_iff_uniqueCaptureCount_pos
      (censusCatalog stage) (0 : Fin 1) (by decide)

#check (systemTheorem :
  (∀ stage : Bool, systemReadout stage =
    (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)) ∧
  ∀ stage : Bool,
    (censusCatalog stage).LowersEscape (0 : Fin 1) ↔
      0 < (censusCatalog stage).uniqueCaptureCount (0 : Fin 1))

example : SystemCharacterization ↔
    (∀ stage : Bool,
      (censusCatalog stage).LowersEscape (0 : Fin 1) ↔
        0 < (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)) :=
  Iff.rfl

example : systemReadout false = 0 := by decide
example : systemReadout true = 2 := by decide

#seal_information_theory

#check systemTheorem.__lowers_escape

#print axioms systemTheorem.__lowers_escape

example :
    arena.__information_catalog.uniqueCaptureCount (0 : Fin 1) = 2 := by
  decide

end LeanInformationAudit.Tests.SealSystemTheorem
