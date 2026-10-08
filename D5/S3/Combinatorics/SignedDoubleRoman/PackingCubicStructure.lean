/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingCubicStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingCubicStructure
   mirror-E: none(waiver:cubic-local-structure)
   anchors: []
   utility: none
   digest: Three distinct neighbours force disjoint edge types and classify domination triangles. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingCubicStructure

open Finset MixedDefs PackingSaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the remaining cubic case all three distinct neighbours exhaust the degree budget. -/
theorem cubic_union (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (S : Finset V) (hdegree : DegreeBound C D S)
    (hlow : ∀ u ∈ S, ¬(C.neighborFinset u ∪ D.neighborFinset u).card ≤ 2) :
    ∀ u ∈ S, (C.neighborFinset u ∪ D.neighborFinset u).card = 3 ∧
      Disjoint (C.neighborFinset u) (D.neighborFinset u) := by
  intro u hu
  have hsize := card_union_le (C.neighborFinset u) (D.neighborFinset u)
  have hdeg := hdegree u hu
  change (C.neighborFinset u).card + (D.neighborFinset u).card ≤ 3 at hdeg
  have hnot := hlow u hu
  have hcard : (C.neighborFinset u ∪ D.neighborFinset u).card = 3 := by omega
  refine ⟨hcard, ?_⟩
  have he := card_union_add_card_inter (C.neighborFinset u) (D.neighborFinset u)
  have hzero : (C.neighborFinset u ∩ D.neighborFinset u).card = 0 := by omega
  exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hzero)

/-- Removing the other end of a cubic edge leaves a pair of distinct neighbours. -/
theorem edge_other_neighbours (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u v : V)
    (hcard : (C.neighborFinset u ∪ D.neighborFinset u).card = 3)
    (huv : C.Adj u v ∨ D.Adj u v) :
    ∃ a b, [u, v, a, b].Nodup ∧ C.neighborFinset u ∪ D.neighborFinset u = {v, a, b} := by
  classical
  let N := C.neighborFinset u ∪ D.neighborFinset u
  have hvN : v ∈ N := by simpa only [N, mem_union, SimpleGraph.mem_neighborFinset] using huv
  have huN : u ∉ N := by simp [N]
  have he : (N.erase v).card = 2 := by rw [card_erase_of_mem hvN, hcard]
  obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp he
  have haN : a ∈ N := mem_of_mem_erase (show a ∈ N.erase v by rw [heq]; simp)
  have hbN : b ∈ N := mem_of_mem_erase (show b ∈ N.erase v by rw [heq]; simp)
  have hav : a ≠ v := (mem_erase.mp (show a ∈ N.erase v by rw [heq]; simp)).1
  have hbv : b ≠ v := (mem_erase.mp (show b ∈ N.erase v by rw [heq]; simp)).1
  have hua : u ≠ a := fun h => huN (h.symm ▸ haN)
  have hub : u ≠ b := fun h => huN (h.symm ▸ hbN)
  have huvne : u ≠ v := huv.elim SimpleGraph.Adj.ne SimpleGraph.Adj.ne
  refine ⟨a, b, ?_, ?_⟩
  · simp [List.nodup_cons, huvne, hua, hub, hav.symm, hbv.symm, hab]
  · rw [← heq, insert_erase hvN]

/-- The two pairs at a domination edge have zero, one, or two common vertices. -/
theorem edge_triangle_cases (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (u v : V)
    (hu : (C.neighborFinset u ∪ D.neighborFinset u).card = 3)
    (hv : (C.neighborFinset v ∪ D.neighborFinset v).card = 3) (huv : D.Adj u v) :
    (∃ w z, [u, v, w, z].Nodup ∧
      C.neighborFinset u ∪ D.neighborFinset u = {v, w, z} ∧
      C.neighborFinset v ∪ D.neighborFinset v = {u, w, z}) ∨
    (∃ w a b, [u, v, w, a, b].Nodup ∧
      C.neighborFinset u ∪ D.neighborFinset u = {v, w, a} ∧
      C.neighborFinset v ∪ D.neighborFinset v = {u, w, b}) ∨
    (∃ a b c d, [u, v, a, b, c, d].Nodup ∧
      C.neighborFinset u ∪ D.neighborFinset u = {v, a, b} ∧
      C.neighborFinset v ∪ D.neighborFinset v = {u, c, d}) := by
  classical
  obtain ⟨a, b, hab, hNu⟩ := edge_other_neighbours C D u v hu (Or.inr huv)
  obtain ⟨c, d, hcd, hNv⟩ := edge_other_neighbours C D v u hv (Or.inr huv.symm)
  have hbase : u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b ∧ a ≠ b := by
    simpa [List.nodup_cons, List.mem_cons, List.mem_singleton, and_assoc] using hab
  have hbase' : v ≠ u ∧ v ≠ c ∧ v ≠ d ∧ u ≠ c ∧ u ≠ d ∧ c ≠ d := by
    simpa [List.nodup_cons, List.mem_cons, List.mem_singleton, and_assoc] using hcd
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d
      exact Or.inl ⟨a, b, hab, hNu, hNv⟩
    · exact Or.inr (Or.inl ⟨a, b, d, by
        simp_all [List.nodup_cons, List.mem_cons, List.mem_singleton, ne_comm], hNu, hNv⟩)
  by_cases had : a = d
  · subst d
    by_cases hbc : b = c
    · subst c
      exact Or.inl ⟨a, b, hab, hNu, by simpa only [pair_comm] using hNv⟩
    · exact Or.inr (Or.inl ⟨a, b, c, by
        simp_all [List.nodup_cons, List.mem_cons, List.mem_singleton, ne_comm],
          hNu, by simpa only [pair_comm] using hNv⟩)
  by_cases hbc : b = c
  · subst c
    exact Or.inr (Or.inl ⟨b, a, d, by
      simp_all [List.nodup_cons, List.mem_cons, List.mem_singleton, ne_comm],
        by simpa only [pair_comm] using hNu, hNv⟩)
  by_cases hbd : b = d
  · subst d
    exact Or.inr (Or.inl ⟨b, a, c, by
      simp_all [List.nodup_cons, List.mem_cons, List.mem_singleton, ne_comm],
        by simpa only [pair_comm] using hNu, by simpa only [pair_comm] using hNv⟩)
  exact Or.inr (Or.inr ⟨a, b, c, d, by
    simp_all [List.nodup_cons, List.mem_cons, List.mem_singleton, ne_comm], hNu, hNv⟩)

end D5.S3.Combinatorics.SignedDoubleRoman.PackingCubicStructure
