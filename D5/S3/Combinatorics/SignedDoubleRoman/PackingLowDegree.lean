/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingLowDegree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingLowDegree
   mirror-E: none(waiver:mixed-packing-low-degree-reduction)
   anchors: []
   utility: none
   digest: Selecting a low-degree vertex produces at most two capacity-enforcing centres. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingLowDegree

open MixedDefs PackingSaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete the closed union neighbourhood of a vertex with at most two distinct neighbours. -/
theorem low_neighbourhood_reduction (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u : V)
    (hdegree : ∀ x ∈ insert u (C.neighborFinset u ∪ D.neighborFinset u),
      C.degree x + D.degree x ≤ 3)
    (hlow : (C.neighborFinset u ∪ D.neighborFinset u).card ≤ 2) :
    let R := insert u (C.neighborFinset u ∪ D.neighborFinset u)
    R.card ≤ 3 ∧ C.IsIndepSet ({u} : Set V) ∧
      (C.neighborFinset u ∪ D.neighborFinset u ⊆ R) ∧
      (∀ x ∈ R,
        ((insert x (D.neighborFinset x)) ∩ ({u} : Finset V)).card ≤ 2 ∧
        (((insert x (D.neighborFinset x)) ∩ ({u} : Finset V)).card = 2 →
          D.neighborFinset x \ R = ∅) ∧ (D.neighborFinset x \ R).card ≤ 2) := by
  classical
  dsimp only
  refine ⟨?_, ?_, Finset.subset_insert _ _, ?_⟩
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro a ha b hb hab
    simp only [Set.mem_singleton_iff] at ha hb
    exact (hab (ha.trans hb.symm)).elim
  · intro x hx
    have hsmall : ((insert x (D.neighborFinset x)) ∩ ({u} : Finset V)).card ≤ 1 := by
      exact (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
    refine ⟨by omega, by omega, ?_⟩
    by_cases hxu : x = u
    · subst x
      have hsub : D.neighborFinset u ⊆ insert u
          (C.neighborFinset u ∪ D.neighborFinset u) :=
        Finset.subset_union_right.trans (Finset.subset_insert _ _)
      rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub]
      simp
    · have hedge : C.Adj x u ∨ D.Adj x u := by
        have hx' := Finset.mem_insert.mp hx
        rcases hx' with hx' | hx'
        · exact (hxu hx').elim
        · simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset] at hx'
          exact hx'.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)
      have hsurv := surviving_degree_le_two C D x
        (insert u (C.neighborFinset u ∪ D.neighborFinset u)) (hdegree x hx)
        ⟨u, Finset.mem_insert_self _ _, hedge⟩
      exact (Finset.card_le_card (Finset.sdiff_subset_sdiff
        Finset.subset_union_right (Finset.Subset.refl _))).trans hsurv

/-- Every imposed pair in this reduction belongs to a distinct domination neighbour of the core. -/
theorem low_imposing_centre (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u r : V)
    (hcapacity : ((insert r (D.neighborFinset r)) ∩ ({u} : Finset V)).card = 1)
    (hsurv : (D.neighborFinset r \
      insert u (C.neighborFinset u ∪ D.neighborFinset u)).card = 2) :
    r ≠ u ∧ D.Adj r u := by
  classical
  have hne : r ≠ u := by
    intro heq
    subst r
    have hsub : D.neighborFinset u ⊆ insert u
        (C.neighborFinset u ∪ D.neighborFinset u) :=
      Finset.subset_union_right.trans (Finset.subset_insert _ _)
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at hsurv
    simp at hsurv
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
    0 < ((insert r (D.neighborFinset r)) ∩ ({u} : Finset V)).card)
  have hx' := Finset.mem_inter.mp hx
  have hxu := Finset.mem_singleton.mp hx'.2
  subst x
  rcases Finset.mem_insert.mp hx'.1 with heq | hedge
  · exact (hne heq.symm).elim
  · exact ⟨hne, (D.mem_neighborFinset r u).mp hedge⟩

end D5.S3.Combinatorics.SignedDoubleRoman.PackingLowDegree
