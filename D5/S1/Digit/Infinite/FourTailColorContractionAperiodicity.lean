/- GID: D5/S1/Digit/Infinite/FourTailColorContractionAperiodicity
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/FourTailColorContractionAperiodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four actual tail colors prohibit nontrivial cycles under an inward outer branch. -/

import D5.S1.Digit.Infinite.FixedTailClosedBudget
import D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction
import D5.S1.Digit.Infinite.OddColorThreeSource
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.FourTailColorContractionAperiodicity

open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction
  (labelIndex label_index_injective)
open D5.S1.Digit.Infinite.OddColorThreeSource (golden_relations)
open Function

local notation "I" => stateInterval true
local notation "X" => stateInterval false
local notation "embed" => (Fin.castLE (by decide : 4 ≤ 5) : Fin 4 → Fin 5)

/-- Exact decoding of all legal closed branches, with the normalized endpoint colors.
Colors one through five are represented by zero through four in `Fin 5`. -/
structure DecoderContract (Q : ℝ → Fin 5) (D : Fin 5 → Fin 5 → Label) : Prop where
  decode : ∀ (a : Label) (y : ℝ), y ∈ stateInterval (outgoing a) →
    D (Q (branch a y)) (Q y) = a
  endpoints : Q (-t ^ 2) = 0 ∧ Q g = 1 ∧ Q t = 2 ∧ Q (2 * t) = 3 ∧
    Q (1 + t) = 4 ∧ Q (-1) = 3

private theorem tail_bound (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    {y : ℝ} (hy : y ∈ I) : (Q y).val < 4 := by
  obtain ⟨c, hc⟩ := hs ▸ Set.mem_image_of_mem Q hy
  rw [← hc]
  exact c.isLt

/-- The four-color restriction of the actual scalar coloring on the closed tail interval. -/
noncomputable def tailColor (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (y : I) : Fin 4 := ⟨(Q y.val).val, tail_bound Q hs y.property⟩

private theorem tail_color_embed (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (y : I) : embed (tailColor Q hs y) = Q y := by
  apply Fin.ext
  rfl

private theorem tail_represented (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (c : Fin 4) : ∃ y : I, tailColor Q hs y = c := by
  have hc : embed c ∈ Q '' I := hs ▸ Set.mem_range_self c
  obtain ⟨y, hy, he⟩ := hc
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Fin.ext
  exact congrArg Fin.val he

private noncomputable def representative (Q : ℝ → Fin 5)
    (hs : Q '' I = Set.range embed) (c : Fin 4) : I :=
  Classical.choose (tail_represented Q hs c)

private theorem inward_maps (i : Fin 3) :
    Set.MapsTo (branch (labelIndex (i.castLE (by decide)))) I I := by
  have hpath : SourcePath true [labelIndex (i.castLE (by decide))]
      (outgoing (labelIndex (i.castLE (by decide)))) := by
    apply SourcePath.cons _ (SourcePath.nil _)
    refine ⟨?_, rfl⟩
    intro _
    fin_cases i <;> norm_num [labelIndex, threeLabel, nullLabel, fiveLabel]
  intro y hy
  apply source_path_maps hpath
  cases h : outgoing (labelIndex (i.castLE (by decide)))
  · exact state_subset true hy
  · exact hy

/-- The unique inward output color of a tail-color column, realized by an actual tail. -/
noncomputable def branchColor (Q : ℝ → Fin 5) (hs : Q '' I = Set.range embed)
    (i : Fin 3) (c : Fin 4) : Fin 4 :=
  tailColor Q hs ⟨branch (labelIndex (i.castLE (by decide))) (representative Q hs c),
    inward_maps i (representative Q hs c).property⟩

end D5.S1.Digit.Infinite.FourTailColorContractionAperiodicity
