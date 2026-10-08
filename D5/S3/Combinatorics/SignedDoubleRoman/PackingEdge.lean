/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingEdge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingEdge
   mirror-E: none(waiver:domination-edge-deletion)
   anchors: []
   utility: none
   digest: Domination edges with zero or one common neighbour yield six-for-two reductions. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingEdge

open MixedDefs PackingSaturation Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Common domination neighbours are the only centres that can exhaust the selected capacity. -/
theorem edge_local_capacity (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u v : V) (R : Finset V)
    (huv : D.Adj u v) (hcolour : ¬ C.Adj u v)
    (hdegree : ∀ x ∈ R, C.degree x + D.degree x ≤ 3)
    (hu : C.neighborFinset u ∪ D.neighborFinset u ⊆ R)
    (hv : C.neighborFinset v ∪ D.neighborFinset v ⊆ R)
    (hlost : ∀ x ∈ R, ∃ t ∈ R, C.Adj x t ∨ D.Adj x t)
    (hcommon : ∀ x, D.Adj x u → D.Adj x v → D.neighborFinset x ⊆ R) :
    C.IsIndepSet (({u, v} : Finset V) : Set V) ∧
      (∀ x ∈ ({u, v} : Finset V), C.neighborFinset x ∪ D.neighborFinset x ⊆ R) ∧
      (∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card ≤ 2 ∧
        (((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card = 2 →
          D.neighborFinset x \ R = ∅) ∧ (D.neighborFinset x \ R).card ≤ 2) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact C.irrefl
    · exact hcolour
    · exact fun h => hcolour h.symm
    · exact C.irrefl
  · intro x hx
    rcases mem_insert.mp hx with hx | hx
    · subst x
      exact hu
    · have hxv := mem_singleton.mp hx
      subst x
      exact hv
  · intro x hx
    have hsmall : ((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card ≤ 2 :=
      (card_le_card inter_subset_right).trans card_le_two
    refine ⟨hsmall, ?_, ?_⟩
    · intro htwo
      apply sdiff_eq_empty_iff_subset.mpr
      by_cases hxu : x = u
      · subst x
        exact subset_union_right.trans hu
      by_cases hxv : x = v
      · subst x
        exact subset_union_right.trans hv
      have heq : (insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V) = {u, v} :=
        eq_of_subset_of_card_le inter_subset_right (by rw [htwo, card_pair huv.ne])
      have hDu : D.Adj x u := by
        have hh : u ∈ insert x (D.neighborFinset x) :=
          (mem_inter.mp (show u ∈ (insert x (D.neighborFinset x)) ∩ {u, v} by
            rw [heq]; simp)).1
        rcases mem_insert.mp hh with hh | hh
        · exact (hxu hh.symm).elim
        · exact (D.mem_neighborFinset _ _).mp hh
      have hDv : D.Adj x v := by
        have hh : v ∈ insert x (D.neighborFinset x) :=
          (mem_inter.mp (show v ∈ (insert x (D.neighborFinset x)) ∩ {u, v} by
            rw [heq]; simp)).1
        rcases mem_insert.mp hh with hh | hh
        · exact (hxv hh.symm).elim
        · exact (D.mem_neighborFinset _ _).mp hh
      exact hcommon x hDu hDv
    · exact (card_le_card (sdiff_subset_sdiff subset_union_right (Subset.refl _))).trans
        (surviving_degree_le_two C D x R (hdegree x hx) (hlost x hx))

/-- A triangle-free domination edge deletes its six closed-union vertices and selects its ends. -/
theorem no_triangle_reduction (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u v a b c d : V)
    (hdist : [u, v, a, b, c, d].Nodup)
    (hdegree : ∀ x ∈ ({u, v, a, b, c, d} : Finset V), C.degree x + D.degree x ≤ 3)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, a, b})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, c, d}) (huv : D.Adj u v) :
    let R : Finset V := {u, v, a, b, c, d}
    let Q : Finset V := {u, v}
    R.card = 6 ∧ C.IsIndepSet (Q : Set V) ∧
      (∀ x ∈ Q, C.neighborFinset x ∪ D.neighborFinset x ⊆ R) ∧
      (∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ Q).card ≤ 2 ∧
        (((insert x (D.neighborFinset x)) ∩ Q).card = 2 →
          D.neighborFinset x \ R = ∅) ∧ (D.neighborFinset x \ R).card ≤ 2) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, and_true, not_or] at hdist
  have huedges : ∀ t ∈ ({v, a, b} : Finset V), C.Adj u t ∨ D.Adj u t := by
    intro t ht
    rw [← hu] at ht
    simpa only [mem_union, SimpleGraph.mem_neighborFinset] using ht
  have hdisju := (exhaust_neighbors C D u {v, a, b} (hdegree u (by simp))
    (by simp_all) huedges).2
  have hnocolour : ¬ C.Adj u v := by
    intro h
    exact disjoint_left.mp hdisju ((C.mem_neighborFinset _ _).mpr h)
      ((D.mem_neighborFinset _ _).mpr huv)
  have hNu : C.neighborFinset u ∪ D.neighborFinset u ⊆
      ({u, v, a, b, c, d} : Finset V) := by
    rw [hu]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    tauto
  have hNv : C.neighborFinset v ∪ D.neighborFinset v ⊆
      ({u, v, a, b, c, d} : Finset V) := by
    rw [hv]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    tauto
  dsimp only
  refine ⟨by simp_all, edge_local_capacity C D u v _ huv hnocolour hdegree hNu hNv ?_ ?_⟩
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with hx | hx | hx | hx | hx | hx <;> subst x
    · exact ⟨v, by simp, Or.inr huv⟩
    · exact ⟨u, by simp, Or.inr huv.symm⟩
    · exact ⟨u, by simp, (huedges a (by simp)).elim
        (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    · exact ⟨u, by simp, (huedges b (by simp)).elim
        (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    · have hh : C.Adj v c ∨ D.Adj v c := by
        have hmem : c ∈ C.neighborFinset v ∪ D.neighborFinset v := by
          rw [hv]
          simp
        simpa only [mem_union, SimpleGraph.mem_neighborFinset] using hmem
      exact ⟨v, by simp, hh.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    · have hh : C.Adj v d ∨ D.Adj v d := by
        have hmem : d ∈ C.neighborFinset v ∪ D.neighborFinset v := by
          rw [hv]
          simp
        simpa only [mem_union, SimpleGraph.mem_neighborFinset] using hmem
      exact ⟨v, by simp, hh.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  · intro x hxu hxv
    have hx1 : x ∈ ({v, a, b} : Finset V) := by
      rw [← hu]
      exact mem_union_right _ ((D.mem_neighborFinset _ _).mpr hxu.symm)
    have hx2 : x ∈ ({u, c, d} : Finset V) := by
      rw [← hv]
      exact mem_union_right _ ((D.mem_neighborFinset _ _).mpr hxv.symm)
    simp only [mem_insert, mem_singleton] at hx1 hx2
    rcases hx1 with hx1 | hx1 | hx1 <;> subst x <;> simp_all <;> aesop

/-- The common neighbour absorbs both selected ends; its third neighbour is also deleted. -/
theorem one_triangle_reduction (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u v w a b c : V)
    (hdist : [u, v, w, a, b].Nodup)
    (hdegree : ∀ x ∈ ({u, v, w, a, b, c} : Finset V), C.degree x + D.degree x ≤ 3)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, w, a})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, w, b})
    (hw : C.neighborFinset w ∪ D.neighborFinset w = {u, v, c}) (huv : D.Adj u v) :
    let R : Finset V := {u, v, w, a, b, c}
    let Q : Finset V := {u, v}
    R.card ≤ 6 ∧ C.IsIndepSet (Q : Set V) ∧
      (∀ x ∈ Q, C.neighborFinset x ∪ D.neighborFinset x ⊆ R) ∧
      (∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ Q).card ≤ 2 ∧
        (((insert x (D.neighborFinset x)) ∩ Q).card = 2 →
          D.neighborFinset x \ R = ∅) ∧ (D.neighborFinset x \ R).card ≤ 2) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, and_true, not_or] at hdist
  have hedu : ∀ t ∈ ({v, w, a} : Finset V), C.Adj u t ∨ D.Adj u t := by
    intro t ht
    rw [← hu] at ht
    simpa only [mem_union, SimpleGraph.mem_neighborFinset] using ht
  have hdisju := (exhaust_neighbors C D u {v, w, a} (hdegree u (by simp))
    (by simp_all) hedu).2
  have hnocolour : ¬ C.Adj u v := by
    intro h
    exact disjoint_left.mp hdisju ((C.mem_neighborFinset _ _).mpr h)
      ((D.mem_neighborFinset _ _).mpr huv)
  have hNu : C.neighborFinset u ∪ D.neighborFinset u ⊆
      ({u, v, w, a, b, c} : Finset V) := by
    rw [hu]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    tauto
  have hNv : C.neighborFinset v ∪ D.neighborFinset v ⊆
      ({u, v, w, a, b, c} : Finset V) := by
    rw [hv]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    tauto
  have hNw : C.neighborFinset w ∪ D.neighborFinset w ⊆
      ({u, v, w, a, b, c} : Finset V) := by
    rw [hw]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    tauto
  dsimp only
  refine ⟨?_, edge_local_capacity C D u v _ huv hnocolour hdegree hNu hNv ?_ ?_⟩
  · have h1 := card_insert_le u ({v, w, a, b, c} : Finset V)
    have h2 := card_insert_le v ({w, a, b, c} : Finset V)
    have h3 := card_insert_le w ({a, b, c} : Finset V)
    have h4 := card_insert_le a ({b, c} : Finset V)
    have h5 := card_le_two (a := b) (b := c)
    omega
  · intro x hx
    have hchoice : x = u ∨ x = v ∨ x ∈ C.neighborFinset u ∪ D.neighborFinset u ∨
        x ∈ C.neighborFinset v ∪ D.neighborFinset v ∨
        x ∈ C.neighborFinset w ∪ D.neighborFinset w := by
      rw [hu, hv, hw]
      simp only [mem_insert, mem_singleton] at hx ⊢
      tauto
    rcases hchoice with rfl | rfl | hx | hx | hx
    · exact ⟨v, by simp, Or.inr huv⟩
    · exact ⟨u, by simp, Or.inr huv.symm⟩
    · simp only [mem_union, SimpleGraph.mem_neighborFinset] at hx
      exact ⟨u, by simp, hx.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    · simp only [mem_union, SimpleGraph.mem_neighborFinset] at hx
      exact ⟨v, by simp, hx.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    · simp only [mem_union, SimpleGraph.mem_neighborFinset] at hx
      exact ⟨w, by simp, hx.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  · intro x hxu hxv
    have hx1 : x ∈ ({v, w, a} : Finset V) := by
      rw [← hu]
      exact mem_union_right _ ((D.mem_neighborFinset _ _).mpr hxu.symm)
    have hx2 : x ∈ ({u, w, b} : Finset V) := by
      rw [← hv]
      exact mem_union_right _ ((D.mem_neighborFinset _ _).mpr hxv.symm)
    have hxw : x = w := by
      simp only [mem_insert, mem_singleton] at hx1 hx2
      rcases hx1 with hx1 | hx1 | hx1 <;> subst x <;> simp_all <;> aesop
    subst x
    exact subset_union_right.trans hNw

/-- A pair-imposing centre lies at a selected end, rather than at an end itself. -/
theorem edge_imposing_centre (D : SimpleGraph V)
    [DecidableRel D.Adj] (u v r : V) (R : Finset V)
    (hu : D.neighborFinset u ⊆ R) (hv : D.neighborFinset v ⊆ R)
    (hcapacity : ((insert r (D.neighborFinset r)) ∩ ({u, v} : Finset V)).card = 1)
    (hsurv : (D.neighborFinset r \ R).card = 2) :
    r ≠ u ∧ r ≠ v ∧ (D.Adj r u ∨ D.Adj r v) := by
  classical
  have hru : r ≠ u := by
    intro h
    subst r
    rw [sdiff_eq_empty_iff_subset.mpr hu, card_empty] at hsurv
    omega
  have hrv : r ≠ v := by
    intro h
    subst r
    rw [sdiff_eq_empty_iff_subset.mpr hv, card_empty] at hsurv
    omega
  obtain ⟨x, hx⟩ := card_pos.mp (by omega :
    0 < ((insert r (D.neighborFinset r)) ∩ ({u, v} : Finset V)).card)
  refine ⟨hru, hrv, ?_⟩
  have hxQ := (mem_inter.mp hx).2
  have hxclosed := (mem_inter.mp hx).1
  simp only [mem_insert, mem_singleton] at hxQ
  rcases hxQ with hxQ | hxQ <;> subst x
  · rcases mem_insert.mp hxclosed with hh | hh
    · exact (hru hh.symm).elim
    · exact Or.inl ((D.mem_neighborFinset _ _).mp hh)
  · rcases mem_insert.mp hxclosed with hh | hh
    · exact (hrv hh.symm).elim
    · exact Or.inr ((D.mem_neighborFinset _ _).mp hh)

end D5.S3.Combinatorics.SignedDoubleRoman.PackingEdge
