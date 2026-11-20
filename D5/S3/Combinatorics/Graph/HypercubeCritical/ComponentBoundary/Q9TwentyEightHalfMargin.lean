/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyEightHalfMargin
   generality: G
   mirror-B: none(waiver:standalone-research-source)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The twenty-six-point exclusion raises both parity margins in a seventy-two-point support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallComponentBoundary142
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixHalfEmbedding

/-! Excluding twenty-point halves raises the parity margins of order-72 supports. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwentyEightHalfMargin

attribute [local instance] Classical.propDecidable

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open CoordinateHalves.BalancedHalfCardinality (half_cardinality)
open CoordinateHalves.Q9TwentySixHalfEmbedding (exists_twenty_cut_of_twenty_six)
open Q9ParityFoldedBoundary (parityPart coordinate_half_parity_bounds)
open private half_card_ge_26_of_no_twenty_half from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallComponentBoundary142
open private reindex reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

private theorem half_card_ge_28 {C : Finset (Q 9)}
    (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (h20 : ∀ (j : Fin 9) (b : Bool), (C.filter fun x => x j = b).card ≠ 20)
    (j : Fin 9) (b : Bool) :
    28 ≤ (C.filter fun x => x j = b).card := by
  classical
  have hlower := half_card_ge_26_of_no_twenty_half hC hr hb h20 j b
  have h72 : C.card = 6 * 12 := hC
  have heven := (half_cardinality h72 hr hb j b).2
  have hne : (C.filter fun x => x j = b).card ≠ 26 := by
    intro he
    let e := Equiv.swap j (0 : Fin 9)
    let T := C.image (reindex e)
    have hT : T.card = 72 := by
      rw [show T = C.image (reindex e) from rfl, card_image_of_injective _ (reindex e).injective, hC]
    have hslice : (coordinateSlice T b).card = 26 := by
      rw [show coordinateSlice T b = (C.filter fun x => x j = b).image (reindex e) from
        reindex_slice C j b, card_image_of_injective _ (reindex e).injective, he]
    obtain ⟨k, c, hcut⟩ :=
      exists_twenty_cut_of_twenty_six hT (reindex_regular hr e) (reindex_balanced hb e) b hslice
    have hpre : (C.filter fun x => x (e.symm k) = c).card = 20 := by
      change ((C.image (reindex e)).filter fun y => y k = c).card = 20 at hcut
      rw [Finset.filter_image, card_image_of_injective _ (reindex e).injective] at hcut
      exact hcut
    exact h20 (e.symm k) c hpre
  omega

/-- Each parity side of every coordinate half contains at least twelve points
in a seventy-two-point support whose coordinate halves exclude size twenty. -/
theorem twelve_le_coordinate_half_parity {C : Finset (Q 9)}
    (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (h20 : ∀ (j : Fin 9) (b : Bool), (C.filter fun x => x j = b).card ≠ 20)
    (j : Fin 9) (b p : Bool) :
    12 ≤ (parityPart (C.filter fun x => x j = b) p).card := by
  have h72 : C.card = 6 * 12 := hC
  have hsize := half_card_ge_28 hC hr hb h20 j b
  have ⟨_, hbalance, _⟩ := coordinate_half_parity_bounds h72 hr hb j b p
  omega

#print axioms twelve_le_coordinate_half_parity

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwentyEightHalfMargin
