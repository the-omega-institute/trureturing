/- GID: D5/S3/ConceptDynamics/InformationEscape/SystemUnit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/SystemUnit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean coordinate CUTs yield a discrete kernel and positive capture. -/

import D5.S3.ConceptDynamics.InformationEscape.StructuralNovelty

/- Library-search audit trail (2026-09-04):
   * Repository searches under `D5` for catalog irredundancy, Boolean-pair
     coordinate bundles, and positive unique capture found the private examples
     in `TheoremUnit`, `EscapePairs`, and `ExactRate`, but no public theorem to reuse.
   * Exact current-tree hits `CIRPT.offDiagonalPairs`,
     `PrimitiveRealization.toPrimitiveBundle`, and `PrimitiveBundle.agrees`
     supply the executable statement below.
   * Pinned Mathlib's finite `Decidable` instances discharge the concrete
     four-state calculation; no duplicate kernel or counting lemma is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.SystemUnit

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

/-- The two CUT slots and empty anchor family for the Boolean-pair arena. -/
abbrev boolPairFstSndSignature : PrimitiveSignature (Bool × Bool) where
  Index := Fin 2
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- The engine arena for the two Boolean coordinate CUTs. -/
def boolPairFstSndArena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool)
  signature := boolPairFstSndSignature
  Law := fun realization =>
    (∀ left right : Bool × Bool,
      (∀ index : Fin 2,
        realization.readout index left = realization.readout index right) ↔
          left = right) ∧
    0 < ((offDiagonalPairs (Bool × Bool)).filter fun pair =>
      ¬(∀ index : Fin 2,
        realization.readout index pair.1 =
          realization.readout index pair.2)).card ∧
    ¬(∀ index : Fin 2,
      realization.readout index (false, false) =
        realization.readout index (true, false))

/-- The first and second projections occupy the two CUT slots. -/
def boolPairFstSndRealization : PrimitiveRealization boolPairFstSndSignature where
  readout := fun index state => if index = 0 then state.1 else state.2
  anchor := fun index => Fin.elim0 index

/-- The concrete discrete-kernel and empty-catalog capture statement. -/
def BoolPairFstSndStatement : Prop :=
  (∀ left right : Bool × Bool,
    (∀ index : Fin 2,
      boolPairFstSndRealization.readout index left =
        boolPairFstSndRealization.readout index right) ↔ left = right) ∧
  0 < ((offDiagonalPairs (Bool × Bool)).filter fun pair =>
    ¬(∀ index : Fin 2,
      boolPairFstSndRealization.readout index pair.1 =
        boolPairFstSndRealization.readout index pair.2)).card ∧
  ¬(∀ index : Fin 2,
    boolPairFstSndRealization.readout index (false, false) =
      boolPairFstSndRealization.readout index (true, false))

/-- The coordinate bundle has the literal four-class discrete kernel, positive
capture against the empty leave-one-out family, and separates `00` from `10`. -/
theorem bool_pair_fst_snd_catalog_irredundant :
    BoolPairFstSndStatement := by
  unfold BoolPairFstSndStatement
  decide

/-- The system theorem is registered through the same legacy-realization interface. -/
theorem bool_pair_fst_snd_catalog_irredundant_realization :
    LegacyPrimitiveRealization boolPairFstSndArena
      BoolPairFstSndStatement
      boolPairFstSndRealization := by
  exact ⟨Iff.rfl⟩

end D5.S3.ConceptDynamics.InformationEscape.SystemUnit
