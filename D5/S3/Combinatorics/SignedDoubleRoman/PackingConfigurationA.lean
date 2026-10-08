/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingConfigurationA
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingConfigurationA
   mirror-E: none(waiver:mixed-packing-diamond-reduction)
   anchors: []
   utility: none
   digest: A colour diamond and its common centre yield a six-for-two clean reduction. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingConfigurationA

open MixedDefs PackingSaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1000000 in
/-- The original five colour edges exhaust the diamond and permit selecting its missing pair. -/
theorem diamond_reduction (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (p q r s u v : V) (hdist : [p, q, r, s, u, v].Nodup)
    (hdegree : ∀ x ∈ ({p, q, r, s, u, v} : Finset V), C.degree x + D.degree x ≤ 3)
    (hpr : C.Adj p r) (hps : C.Adj p s) (hqr : C.Adj q r)
    (hqs : C.Adj q s) (hrs : C.Adj r s)
    (hup : C.Adj u p ∨ D.Adj u p) (huq : C.Adj u q ∨ D.Adj u q)
    (huv : C.Adj u v ∨ D.Adj u v) :
    let R : Finset V := {p, q, r, s, u, v}
    let Q : Finset V := {p, q}
    C.IsIndepSet (Q : Set V) ∧
      (∀ x ∈ Q, C.neighborFinset x ∪ D.neighborFinset x ⊆ R) ∧
      (∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ Q).card +
        (D.neighborFinset x \ R).card ≤ 2) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, not_or] at hdist
  dsimp only
  have hp := exhaust_neighbors C D p {r, s, u} (hdegree p (by simp))
    (by simp_all)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact Or.inl hpr
        · exact Or.inl hps
        · exact hup.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm))
  have hq := exhaust_neighbors C D q {r, s, u} (hdegree q (by simp))
    (by simp_all)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact Or.inl hqr
        · exact Or.inl hqs
        · exact huq.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm))
  have hr := exhaust_colour C D r {p, q, s} (hdegree r (by simp))
    (by simp_all)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hpr.symm
        · exact hqr.symm
        · exact hrs)
  have hs := exhaust_colour C D s {p, q, r} (hdegree s (by simp))
    (by simp_all)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hps.symm
        · exact hqs.symm
        · exact hrs.symm)
  have hu := exhaust_neighbors C D u {p, q, v} (hdegree u (by simp))
    (by simp_all)
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hup
        · exact huq
        · exact huv)
  have hpq : ¬ C.Adj p q := by
    intro h
    have hmem : q ∈ C.neighborFinset p ∪ D.neighborFinset p := by
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      exact Or.inl h
    rw [hp.1] at hmem
    simp_all
  have hsubp : C.neighborFinset p ∪ D.neighborFinset p ⊆
      ({p, q, r, s, u, v} : Finset V) := by
    rw [hp.1]
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    aesop
  have hsubq : C.neighborFinset q ∪ D.neighborFinset q ⊆
      ({p, q, r, s, u, v} : Finset V) := by
    rw [hq.1]
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    aesop
  have hsubu : C.neighborFinset u ∪ D.neighborFinset u ⊆
      ({p, q, r, s, u, v} : Finset V) := by
    rw [hu.1]
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    aesop
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact C.irrefl
    · exact hpq
    · exact fun h ↦ hpq h.symm
    · exact C.irrefl
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hsubp
    · exact hsubq
  · intro x hx
    have hsmall : ((insert x (D.neighborFinset x)) ∩ ({p, q} : Finset V)).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx | hx | hx
    · subst x
      have hd : D.neighborFinset p \ ({p, q, r, s, u, v} : Finset V) = ∅ :=
        Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_union_right.trans hsubp)
      simpa [hd] using hsmall
    · subst x
      have hd : D.neighborFinset q \ ({p, q, r, s, u, v} : Finset V) = ∅ :=
        Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_union_right.trans hsubq)
      simpa [hd] using hsmall
    · subst x
      simpa [hr.2] using hsmall
    · subst x
      simpa [hs.2] using hsmall
    · subst x
      have hd : D.neighborFinset u \ ({p, q, r, s, u, v} : Finset V) = ∅ :=
        Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_union_right.trans hsubu)
      simpa [hd] using hsmall
    · subst x
      have hnop : ¬ D.Adj v p := by
        intro h
        have hmem : v ∈ C.neighborFinset p ∪ D.neighborFinset p := by
          simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
          exact Or.inr h.symm
        rw [hp.1] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        aesop
      have hnoq : ¬ D.Adj v q := by
        intro h
        have hmem : v ∈ C.neighborFinset q ∪ D.neighborFinset q := by
          simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
          exact Or.inr h.symm
        rw [hq.1] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        aesop
      have hclosed : (insert v (D.neighborFinset v)) ∩ ({p, q} : Finset V) = ∅ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty, iff_false, not_and]
        intro hx
        rintro (rfl | rfl) <;> simp_all
      rw [hclosed]
      simp only [Finset.card_empty, Nat.zero_add]
      have hsurv := surviving_degree_le_two C D v {p, q, r, s, u, v}
        (hdegree v (by simp)) ⟨u, by simp,
          huv.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)⟩
      exact (Finset.card_le_card (Finset.sdiff_subset_sdiff
        Finset.subset_union_right (Finset.Subset.refl _))).trans hsurv

end D5.S3.Combinatorics.SignedDoubleRoman.PackingConfigurationA
