/- GID: D5/S3/ConceptDynamics/InformationEscape/SystemUnit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/SystemUnit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The escape engine characterizes its own census on a two-stage arena. -/

import D5.S3.ConceptDynamics.InformationEscape.Laws

/- Library-search audit trail (2026-09-05):
   * `Catalog.lowersEscape_iff_uniqueCaptureCount_pos` is the canonical exact-rate
     characterization consumed by the self-application theorem below.
   * `catalogIrredundant_iff_forall_pos` supplies the catalog-wide companion law.
   * The Stage-indexed catalog uses the existing `cutKernel`, `Catalog`, and
     `uniqueCaptureCount` definitions; it introduces no second census evaluator. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.SystemUnit

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

/-- The finite meta-arena has one stage before and one after separation. -/
abbrev Stage := Bool

/-- The engine census is evaluated over the same two states as the Stage arena. -/
abbrev censusArena : Arena := Arena.ofFintype Bool

private abbrev censusBundle (stage : Stage) : PrimitiveBundle Bool where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => {
    axis := .cut
    kernel := cutKernel fun state => if stage then state else false }

private abbrev censusUnit (stage : Stage) : TheoremUnit censusArena where
  primitives := censusBundle stage
  Statement := True
  proof := True.intro

/-- One theorem unit whose CUT changes from constant to separating by stage. -/
abbrev censusCatalog (stage : Stage) : Catalog censusArena where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt := fun _ => censusUnit stage

/-- The SYSTEM readout is the engine's own leave-one-out unique-capture census. -/
abbrev systemReadout (stage : Stage) : Nat :=
  (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)

/-- The exact-rate engine characterization, specialized at every Stage. -/
abbrev SystemCharacterization : Prop :=
  ∀ stage : Stage,
    (censusCatalog stage).LowersEscape (0 : Fin 1) ↔
      0 < (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)

/-- The primitive-law arena in which the engine analyzes its own census theorem. -/
def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Stage
  signature := {
    Index := Fin 1
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
      SystemCharacterization ∧ CatalogIrredundant (censusCatalog true)

/-- The realization reads the canonical engine census without reimplementing it. -/
def systemRealization : PrimitiveRealization arena.signature where
  readout := fun _ stage =>
    (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)
  anchor := Fin.elim0

/-- The literal SYSTEM statement ties its readout to the engine characterization. -/
def SystemStatement : Prop :=
  (∀ stage,
    systemRealization.readout (0 : Fin 1) stage =
      (censusCatalog stage).uniqueCaptureCount (0 : Fin 1)) ∧
    SystemCharacterization ∧ CatalogIrredundant (censusCatalog true)

/-- Spec 15.1-15.2 / T-013 / T-CIRPT-015 / AC-009: the exact-rate engine
self-registers its `LowersEscape` characterization in the Stage arena. The
canonical census witnesses escape by changing from zero to two. -/
theorem engine_census_self_application : SystemStatement := by
  constructor
  · intro stage
    rfl
  · constructor
    · intro stage
      exact Catalog.lowersEscape_iff_uniqueCaptureCount_pos
        (censusCatalog stage) (0 : Fin 1) (by decide)
    · exact (catalogIrredundant_iff_forall_pos (censusCatalog true)).mpr (by decide)

/-- The self-application theorem uses the legacy registration interface unchanged. -/
theorem system_self_application_realization :
    LegacyPrimitiveRealization arena SystemStatement systemRealization :=
  ⟨Iff.rfl⟩

example : systemReadout false = 0 := by decide

example : systemReadout true = 2 := by decide

end D5.S3.ConceptDynamics.InformationEscape.SystemUnit
