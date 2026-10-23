/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Vertex listings identify the small cubic graphs with standard graph models. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmall
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmallIso

open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmall

/-- The complete graph on four vertices. -/
def modelFour : SimpleGraph (Fin 4) := ⊤

instance : DecidableRel modelFour.Adj := inferInstanceAs (DecidableRel (⊤ : SimpleGraph (Fin 4)).Adj)

/-- The cubic graph complementary to two disjoint triangles. -/
def modelSixTriangles : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun x y => (x.val < 3 ∧ 3 ≤ y.val) ∨ (y.val < 3 ∧ 3 ≤ x.val)

instance : DecidableRel modelSixTriangles.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel
    (fun x y : Fin 6 => (x.val < 3 ∧ 3 ≤ y.val) ∨ (y.val < 3 ∧ 3 ≤ x.val))).Adj)

/-- The cubic graph complementary to the cycle 0,1,2,3,4,5. -/
def modelSixCycle : SimpleGraph (Fin 6) := (SimpleGraph.cycleGraph 6)ᶜ

instance : DecidableRel modelSixCycle.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.cycleGraph 6)ᶜ.Adj)

/-- A four-vertex cubic graph is isomorphic to the standard complete graph. -/
theorem cubic_four_iso {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 4)
    (hdeg : ∀ v, G.degree v = 3) : Nonempty (G ≃g modelFour) := by
  let q : V ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  refine ⟨{ q with map_rel_iff' := ?_ }⟩
  intro x y
  simp [modelFour, cubic_four_complete G hcard hdeg, q.injective.ne_iff]

set_option maxHeartbeats 800000 in
/-- The six-vertex cubic graphs have the complete-bipartite or prism graph form. -/
theorem cubic_six_iso {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 6)
    (hdeg : ∀ v, G.degree v = 3) :
    Nonempty (G ≃g modelSixTriangles) ∨ Nonempty (G ≃g modelSixCycle) := by
  classical
  have hd : ∀ v, Gᶜ.degree v = 2 := by
    intro v
    rw [G.degree_compl, hcard, hdeg]
  obtain ⟨a,b,c,d,e,f,hp,hu,hform⟩ := two_regular_six_presentation Gᶜ hcard hd
  obtain ⟨q,h0,h1,h2,h3,h4,h5⟩ := six_listing_equiv hp hu
  rcases hform with htri | hcyc
  · obtain ⟨ha,hb,hc,hd,he,hf⟩ := htri
    have haQ : (Gᶜ).neighborFinset (q 0) = {q 1,q 2} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) ha
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h0,h1,h2] using Iff.of_eq hm
    have hbQ : (Gᶜ).neighborFinset (q 1) = {q 0,q 2} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hb
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h0,h1,h2] using Iff.of_eq hm
    have hcQ : (Gᶜ).neighborFinset (q 2) = {q 0,q 1} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hc
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h0,h1,h2] using Iff.of_eq hm
    have hdQ : (Gᶜ).neighborFinset (q 3) = {q 4,q 5} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hd
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h3,h4,h5] using Iff.of_eq hm
    have heQ : (Gᶜ).neighborFinset (q 4) = {q 3,q 5} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) he
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h3,h4,h5] using Iff.of_eq hm
    have hfQ : (Gᶜ).neighborFinset (q 5) = {q 3,q 4} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hf
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h3,h4,h5] using Iff.of_eq hm
    have hrel (i j : Fin 6) : (Gᶜ).Adj (q i) (q j) ↔ (modelSixTrianglesᶜ).Adj i j := by
      rw [← (Gᶜ).mem_neighborFinset (q i) (q j)]
      fin_cases i <;> fin_cases j <;>
        simp [haQ,hbQ,hcQ,hdQ,heQ,hfQ,q.injective.eq_iff,
          modelSixTriangles, SimpleGraph.compl_adj, SimpleGraph.fromRel_adj]
    have hm (i j : Fin 6) : G.Adj (q i) (q j) ↔ modelSixTriangles.Adj i j := by
      have := hrel i j
      simp only [SimpleGraph.compl_adj] at this
      by_cases h : i = j
      · subst j; simp
      · have hqne : q i ≠ q j := q.injective.ne h
        exact not_iff_not.mp ⟨fun hG => (this.mp ⟨hqne,hG⟩).2,
          fun hM => (this.mpr ⟨h,hM⟩).2⟩
    have iq : modelSixTriangles ≃g G := { q with map_rel_iff' := fun {i j} => hm i j }
    exact Or.inl ⟨iq.symm⟩
  · obtain ⟨ha,hb,hc,hd,he,hf⟩ := hcyc
    have haQ : (Gᶜ).neighborFinset (q 0) = {q 1,q 5} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) ha
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h0,h1,h5] using Iff.of_eq hm
    have hbQ : (Gᶜ).neighborFinset (q 1) = {q 0,q 2} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hb
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h0,h1,h2] using Iff.of_eq hm
    have hcQ : (Gᶜ).neighborFinset (q 2) = {q 1,q 3} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hc
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h1,h2,h3] using Iff.of_eq hm
    have hdQ : (Gᶜ).neighborFinset (q 3) = {q 2,q 4} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hd
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h2,h3,h4] using Iff.of_eq hm
    have heQ : (Gᶜ).neighborFinset (q 4) = {q 3,q 5} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) he
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h3,h4,h5] using Iff.of_eq hm
    have hfQ : (Gᶜ).neighborFinset (q 5) = {q 4,q 0} := by
      ext x
      have hm := congrArg (fun s : Finset V => x ∈ s) hf
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      simpa only [h0,h4,h5] using Iff.of_eq hm
    have hrel (i j : Fin 6) : (Gᶜ).Adj (q i) (q j) ↔ (modelSixCycleᶜ).Adj i j := by
      rw [← (Gᶜ).mem_neighborFinset (q i) (q j)]
      fin_cases i <;> fin_cases j <;>
        simp [haQ,hbQ,hcQ,hdQ,heQ,hfQ,q.injective.eq_iff,
          modelSixCycle, SimpleGraph.cycleGraph_adj] <;> decide
    have hm (i j : Fin 6) : G.Adj (q i) (q j) ↔ modelSixCycle.Adj i j := by
      have := hrel i j
      simp only [SimpleGraph.compl_adj] at this
      by_cases h : i = j
      · subst j; simp
      · have hqne : q i ≠ q j := q.injective.ne h
        exact not_iff_not.mp ⟨fun hG => (this.mp ⟨hqne,hG⟩).2,
          fun hM => (this.mpr ⟨h,hM⟩).2⟩
    have iq : modelSixCycle ≃g G := { q with map_rel_iff' := fun {i j} => hm i j }
    exact Or.inr ⟨iq.symm⟩

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmallIso
