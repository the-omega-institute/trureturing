/- GID: D5/S3/Combinatorics/Graph/HereditaryFlip/Median
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HereditaryFlip/Median
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Native metric medians of hereditary flip graphs are support majorities and classify flag families. -/

import D5.S3.Combinatorics.Graph.HereditaryFlip.Majority
import D5.S3.Combinatorics.Graph.HereditaryFlip.Metric

/-! # Native metric medians and flag families

The median condition uses the native graph distance on all three intervals.
Connectedness includes nonemptiness; an empty hereditary family is flag but
does not give a median graph under this convention.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.HereditaryFlip.Median

open Majority Metric

/-- A common point of the three native distance intervals. -/
def IsMedian {W : Type*} (G : SimpleGraph W) (A B C M : W) : Prop :=
  G.dist A M + G.dist M B = G.dist A B ∧
  G.dist B M + G.dist M C = G.dist B C ∧
  G.dist C M + G.dist M A = G.dist C A

/-- A connected graph with exactly one common interval point for every triple. -/
def IsMedianGraph {W : Type*} (G : SimpleGraph W) : Prop :=
  G.Connected ∧ ∀ A B C, ∃! M, IsMedian G A B C M

variable {V : Type*} [DecidableEq V]

/-- Native common-interval membership reconstructs exactly the coordinate majority. -/
theorem is_median_iff {K : Set (Finset V)} (hK : IsLowerSet K)
    (A B C M : {S : Finset V // S ∈ K}) :
    IsMedian (flipGraph K) A B C M ↔ M.val = majority A.val B.val C.val := by
  rw [IsMedian, interval_iff hK, interval_iff hK, interval_iff hK]
  constructor
  · rintro ⟨hAB, hBC, hCA⟩
    ext x
    have hablo := @hAB.1 x
    have habup := @hAB.2 x
    have hbclo := @hBC.1 x
    have hbcup := @hBC.2 x
    have hcalo := @hCA.1 x
    have hcaup := @hCA.2 x
    simp only [Finset.mem_inter, Finset.mem_union] at hablo habup hbclo hbcup hcalo hcaup
    simp only [majority, Finset.mem_union, Finset.mem_inter]
    tauto
  · intro hM
    rw [hM]
    simp only [majority, Finset.subset_iff, Finset.mem_union, Finset.mem_inter]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro x hx <;> tauto

/-- A hereditary flip graph is a native median graph exactly when its family
contains the empty support and is determined by its empty, singleton and pair faces. -/
theorem median_graph_iff_flag {K : Set (Finset V)} (hK : IsLowerSet K) :
    IsMedianGraph (flipGraph K) ↔ ∅ ∈ K ∧ Flag K := by
  constructor
  · rintro ⟨hconn, hmedian⟩
    obtain ⟨A⟩ := hconn.nonempty
    refine ⟨hK (Finset.empty_subset A.val) A.property, ?_⟩
    apply (majority_closed_iff_flag hK).mp
    intro A hA B hB C hC
    obtain ⟨M, hM, _⟩ := hmedian ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩
    have heq := (is_median_iff hK _ _ _ M).mp hM
    exact heq ▸ M.property
  · rintro ⟨h0, hflag⟩
    refine ⟨connected hK h0, ?_⟩
    intro A B C
    have hclosed := (majority_closed_iff_flag hK).mpr hflag
    refine ⟨⟨majority A.val B.val C.val,
      hclosed _ A.property _ B.property _ C.property⟩, ?_, ?_⟩
    · exact (is_median_iff hK _ _ _ _).mpr rfl
    · intro M hM
      exact Subtype.ext ((is_median_iff hK _ _ _ M).mp hM)

end D5.S3.Combinatorics.Graph.HereditaryFlip.Median
