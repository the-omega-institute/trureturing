/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingSaturation
   mirror-E: none(waiver:mixed-packing-degree-exhaustion)
   anchors: []
   utility: none
   digest: Degree exhaustion controls saturated neighborhoods and deleted boundary capacity. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation

open MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Three distinct neighbours exhaust both degree budgets and exclude parallel edge types. -/
theorem exhaust_neighbors (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (v : V) (K : Finset V) (hdegree : C.degree v + D.degree v ≤ 3)
    (hcard : K.card = 3)
    (hedges : ∀ w ∈ K, C.Adj v w ∨ D.Adj v w) :
    (C.neighborFinset v ∪ D.neighborFinset v = K) ∧
      Disjoint (C.neighborFinset v) (D.neighborFinset v) := by
  have hsub : K ⊆ C.neighborFinset v ∪ D.neighborFinset v := by
    intro w hw
    simpa only [Finset.mem_union, SimpleGraph.mem_neighborFinset] using hedges w hw
  have hlow := Finset.card_le_card hsub
  have hupp := Finset.card_union_le (C.neighborFinset v) (D.neighborFinset v)
  have hsum := Finset.card_union_add_card_inter (C.neighborFinset v) (D.neighborFinset v)
  have hunion : (C.neighborFinset v ∪ D.neighborFinset v).card = K.card := by
    change (C.neighborFinset v).card + (D.neighborFinset v).card ≤ 3 at hdegree
    omega
  refine ⟨(Finset.eq_of_subset_of_card_le hsub (le_of_eq hunion)).symm, ?_⟩
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply Finset.card_eq_zero.mp
  change (C.neighborFinset v).card + (D.neighborFinset v).card ≤ 3 at hdegree
  omega

/-- One deleted neighbour leaves capacity for at most two surviving neighbours of either type. -/
theorem surviving_degree_le_two (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (v : V) (R : Finset V)
    (hdegree : C.degree v + D.degree v ≤ 3)
    (hlost : ∃ w ∈ R, C.Adj v w ∨ D.Adj v w) :
    ((C.neighborFinset v ∪ D.neighborFinset v) \ R).card ≤ 2 := by
  obtain ⟨w, hwR, hwedge⟩ := hlost
  have hw : w ∈ (C.neighborFinset v ∪ D.neighborFinset v) ∩ R := by
    refine Finset.mem_inter.mpr ⟨?_, hwR⟩
    simpa only [Finset.mem_union, SimpleGraph.mem_neighborFinset] using hwedge
  have hpos : 0 < ((C.neighborFinset v ∪ D.neighborFinset v) ∩ R).card :=
    Finset.card_pos.mpr ⟨w, hw⟩
  have hsplit := Finset.card_sdiff_add_card_inter
    (C.neighborFinset v ∪ D.neighborFinset v) R
  have hsum := Finset.card_union_le (C.neighborFinset v) (D.neighborFinset v)
  change (C.neighborFinset v).card + (D.neighborFinset v).card ≤ 3 at hdegree
  omega

omit [DecidableEq V] in
/-- A colour-saturated vertex has no domination edges. -/
theorem exhaust_colour (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (v : V) (K : Finset V) (hdegree : C.degree v + D.degree v ≤ 3)
    (hcard : K.card = 3) (hedges : ∀ w ∈ K, C.Adj v w) :
    C.neighborFinset v = K ∧ D.neighborFinset v = ∅ := by
  have hsub : K ⊆ C.neighborFinset v := by
    intro w hw
    exact (C.mem_neighborFinset v w).mpr (hedges w hw)
  have hlow := Finset.card_le_card hsub
  change (C.neighborFinset v).card + (D.neighborFinset v).card ≤ 3 at hdegree
  have heq : (C.neighborFinset v).card = K.card := by omega
  refine ⟨(Finset.eq_of_subset_of_card_le hsub (le_of_eq heq)).symm, ?_⟩
  apply Finset.card_eq_zero.mp
  omega

end D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation
