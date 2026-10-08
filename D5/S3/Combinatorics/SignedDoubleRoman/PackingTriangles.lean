/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingTriangles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingTriangles
   mirror-E: none(waiver:mixed-packing-double-triangle-reduction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A domination edge in two union triangles admits a clean six-for-two deletion. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingTriangles

open MixedDefs PackingSaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Common neighbours absorb every dangerous closed-neighbourhood constraint. -/
theorem double_triangle_reduction (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u v w z : V)
    (hdist : [u, v, w, z].Nodup) (hdegree : ∀ x, C.degree x + D.degree x ≤ 3)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, w, z})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, w, z})
    (huv : D.Adj u v) :
    let R := ({u, v, w, z} : Finset V) ∪
      (C.neighborFinset w ∪ D.neighborFinset w) ∪
      (C.neighborFinset z ∪ D.neighborFinset z)
    let Q : Finset V := {u, v}
    R.card ≤ 6 ∧ C.IsIndepSet (Q : Set V) ∧
      (∀ x ∈ Q, C.neighborFinset x ∪ D.neighborFinset x ⊆ R) ∧
      (∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ Q).card +
        (D.neighborFinset x \ R).card ≤ 2) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, and_true, not_or] at hdist
  let A : Finset V := {u, v, w, z}
  let Nw := C.neighborFinset w ∪ D.neighborFinset w
  let Nz := C.neighborFinset z ∪ D.neighborFinset z
  let R := A ∪ Nw ∪ Nz
  have hA : A ⊆ R := Finset.subset_union_left.trans Finset.subset_union_left
  have hNw : Nw ⊆ R := Finset.subset_union_right.trans Finset.subset_union_left
  have hNz : Nz ⊆ R := Finset.subset_union_right
  have hNu : C.neighborFinset u ∪ D.neighborFinset u ⊆ R := by
    rw [hu]
    exact (by dsimp [A]; simp : ({v, w, z} : Finset V) ⊆ A) |>.trans hA
  have hNv : C.neighborFinset v ∪ D.neighborFinset v ⊆ R := by
    rw [hv]
    exact (by dsimp [A]; simp : ({u, w, z} : Finset V) ⊆ A) |>.trans hA
  have hedu : ∀ t ∈ ({v, w, z} : Finset V), C.Adj u t ∨ D.Adj u t := by
    intro t ht
    rw [← hu] at ht
    simpa only [Finset.mem_union, SimpleGraph.mem_neighborFinset] using ht
  have hdisju := (exhaust_neighbors C D u {v, w, z} (hdegree u)
    (by simp_all) hedu).2
  have hcolouruv : ¬ C.Adj u v := by
    intro h
    exact Finset.disjoint_left.mp hdisju
      ((C.mem_neighborFinset u v).mpr h) ((D.mem_neighborFinset u v).mpr huv)
  have hloss : ∀ t, t = w ∨ t = z →
      ({u, v} : Finset V) ⊆ (C.neighborFinset t ∪ D.neighborFinset t) ∩ A := by
    intro t ht
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      rcases hx with hx | hx <;> subst x
      · have htu : t ∈ C.neighborFinset u ∪ D.neighborFinset u := by
          rw [hu]; rcases ht with rfl | rfl <;> simp
        simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset] at htu
        exact htu.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)
      · have htv : t ∈ C.neighborFinset v ∪ D.neighborFinset v := by
          rw [hv]; rcases ht with rfl | rfl <;> simp
        simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset] at htv
        exact htv.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)
    · rcases hx with hx | hx <;> subst x <;> simp [A]
  have hremaining : ∀ t, t = w ∨ t = z →
      ((C.neighborFinset t ∪ D.neighborFinset t) \ A).card ≤ 1 := by
    intro t ht
    have htwo := Finset.card_le_card (hloss t ht)
    have hsum := Finset.card_union_le (C.neighborFinset t) (D.neighborFinset t)
    have hsplit := Finset.card_sdiff_add_card_inter
      (C.neighborFinset t ∪ D.neighborFinset t) A
    have hdeg := hdegree t
    change (C.neighborFinset t).card + (D.neighborFinset t).card ≤ 3 at hdeg
    have hpair : ({u, v} : Finset V).card = 2 := by simp_all
    omega
  have hRsize : R.card ≤ 6 := by
    have heq : R = A ∪ (Nw \ A) ∪ (Nz \ A) := by
      ext x
      simp only [R, Finset.mem_union, Finset.mem_sdiff]
      tauto
    rw [heq]
    have hsum1 := Finset.card_union_le A (Nw \ A)
    have hsum2 := Finset.card_union_le (A ∪ (Nw \ A)) (Nz \ A)
    have h1 := hremaining w (Or.inl rfl)
    have h2 := hremaining z (Or.inr rfl)
    have hAc : A.card = 4 := by simp_all [A]
    change (Nw \ A).card ≤ 1 at h1
    change (Nz \ A).card ≤ 1 at h2
    omega
  change R.card ≤ 6 ∧ _
  refine ⟨hRsize, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> subst x <;> rcases hy with rfl | rfl
    · exact C.irrefl
    · exact hcolouruv
    · exact fun h ↦ hcolouruv h.symm
    · exact C.irrefl
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx <;> subst x
    · exact hNu
    · exact hNv
  · intro x hx
    have hsmall : ((insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V)).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
    by_cases hxA : x ∈ A
    · have hsub : D.neighborFinset x ⊆ R := by
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hxA
        rcases hxA with rfl | rfl | rfl | rfl
        · exact Finset.subset_union_right.trans hNu
        · exact Finset.subset_union_right.trans hNv
        · exact Finset.subset_union_right.trans hNw
        · exact Finset.subset_union_right.trans hNz
      have hd := Finset.sdiff_eq_empty_iff_subset.mpr hsub
      rw [hd, Finset.card_empty, Nat.add_zero]
      exact hsmall
    · have hxne : x ≠ u ∧ x ≠ v ∧ x ≠ w ∧ x ≠ z := by simpa [A] using hxA
      have hno : ¬ D.Adj x u ∧ ¬ D.Adj x v := by
        constructor
        · intro h
          have hmem : x ∈ C.neighborFinset u ∪ D.neighborFinset u := by
            simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
            exact Or.inr h.symm
          rw [hu] at hmem
          simp_all
        · intro h
          have hmem : x ∈ C.neighborFinset v ∪ D.neighborFinset v := by
            simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
            exact Or.inr h.symm
          rw [hv] at hmem
          simp_all
      have hclosed : (insert x (D.neighborFinset x)) ∩ ({u, v} : Finset V) = ∅ := by
        ext t
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty, iff_false, not_and]
        intro ht
        rintro (rfl | rfl) <;> simp_all
      rw [hclosed]
      simp only [Finset.card_empty, Nat.zero_add]
      have hlost : ∃ t ∈ R, C.Adj x t ∨ D.Adj x t := by
        have hxN : x ∈ Nw ∨ x ∈ Nz := by
          change x ∈ (A ∪ Nw) ∪ Nz at hx
          rcases Finset.mem_union.mp hx with hh | hh
          · rcases Finset.mem_union.mp hh with hh | hh
            · exact (hxA hh).elim
            · exact Or.inl hh
          · exact Or.inr hh
        rcases hxN with hw | hz
        · refine ⟨w, hA (by simp [A]), ?_⟩
          simp only [Nw, Finset.mem_union, SimpleGraph.mem_neighborFinset] at hw
          exact hw.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)
        · refine ⟨z, hA (by simp [A]), ?_⟩
          simp only [Nz, Finset.mem_union, SimpleGraph.mem_neighborFinset] at hz
          exact hz.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)
      exact (Finset.card_le_card (Finset.sdiff_subset_sdiff
        Finset.subset_union_right (Finset.Subset.refl _))).trans
          (surviving_degree_le_two C D x R (hdegree x) hlost)

end D5.S3.Combinatorics.SignedDoubleRoman.PackingTriangles
