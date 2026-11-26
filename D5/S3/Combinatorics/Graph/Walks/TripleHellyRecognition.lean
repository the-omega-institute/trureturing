/- GID: D5/S3/Combinatorics/Graph/Walks/TripleHellyRecognition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/TripleHellyRecognition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Recognition of trees by triple intersections of connected induced vertex sets. -/
import D5.S3.Combinatorics.Graph.Walks.SubtreeHelly

namespace SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Every native cycle supplies three connected induced vertex sets with pairwise intersections
but no common vertex. Ambient edges outside the cycle, including chords, are unrestricted. -/
theorem Walk.IsCycle.exists_connected_triple_obstruction {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) :
    ∃ A B C : Set V,
      (G.induce A).Connected ∧ (G.induce B).Connected ∧ (G.induce C).Connected ∧
      (A ∩ B).Nonempty ∧ (B ∩ C).Nonempty ∧ (C ∩ A).Nonempty ∧
      A ∩ B ∩ C = ∅ := by
  cases p with
  | nil => exact (hp.ne_nil rfl).elim
  | @cons _ y _ h q =>
    cases q with
    | nil => exact (h.ne rfl).elim
    | @cons _ z _ h' r =>
      have hy : y ∉ r.support := by
        exact (List.nodup_cons.mp hp.support_nodup).1
      have hxz : v ≠ z := by
        intro he
        subst z
        have hn := hp.isTrail.edges_nodup
        simp only [Walk.edges_cons, List.nodup_cons] at hn
        exact hn.1 (by simp)
      refine ⟨{v, y}, {y, z}, {w | w ∈ r.support},
        induce_pair_connected_of_adj h, induce_pair_connected_of_adj h',
        r.connected_induce_support, ?_, ?_, ?_, ?_⟩
      · exact ⟨y, by simp⟩
      · exact ⟨z, by simp⟩
      · exact ⟨v, by simp⟩
      · apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have ha : w = v ∨ w = y := by simpa using hw.1.1
        have hb : w = y ∨ w = z := by simpa using hw.1.2
        rcases ha with rfl | rfl
        · rcases hb with he | he
          · exact h.ne he
          · exact hxz he
        · exact hy hw.2

/-- A connected graph is a tree exactly when every three pairwise intersecting connected induced
vertex sets have a common vertex. The vertex type may be infinite, and sets may repeat. -/
theorem isTree_iff_connected_triple_helly (hG : G.Connected) :
    G.IsTree ↔ ∀ A B C : Set V,
      (G.induce A).Connected → (G.induce B).Connected → (G.induce C).Connected →
      (A ∩ B).Nonempty → (B ∩ C).Nonempty → (C ∩ A).Nonempty →
      (A ∩ B ∩ C).Nonempty := by
  classical
  constructor
  · intro hT A B C hA hB hC hAB hBC hCA
    let a : Fin 3 → Set V := fun i => if i = 0 then A else if i = 1 then B else C
    have hc : ∀ i ∈ (Finset.univ : Finset (Fin 3)), (G.induce (a i)).Connected := by
      intro i _
      fin_cases i <;> dsimp [a] <;> assumption
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        ∀ j ∈ (Finset.univ : Finset (Fin 3)), (a i ∩ a j).Nonempty := by
      intro i _ j _
      fin_cases i <;> fin_cases j <;> dsimp [a]
      all_goals first | exact hAB | exact hBC | exact hCA |
        simpa only [Set.inter_comm] using hAB |
        simpa only [Set.inter_comm] using hBC |
        simpa only [Set.inter_comm] using hCA |
        exact ⟨hAB.choose, hAB.choose_spec.1, hAB.choose_spec.1⟩ |
        exact ⟨hBC.choose, hBC.choose_spec.1, hBC.choose_spec.1⟩ |
        exact ⟨hCA.choose, hCA.choose_spec.1, hCA.choose_spec.1⟩
    obtain ⟨x, hx⟩ := hT.inter_nonempty_of_pairwise Finset.univ_nonempty hc hi
    simp only [Set.mem_iInter, Finset.mem_univ, forall_const] at hx
    exact ⟨x, ⟨hx 0, hx 1⟩, hx 2⟩
  · intro h
    refine ⟨hG, ?_⟩
    intro v p hp
    obtain ⟨A, B, C, hA, hB, hC, hAB, hBC, hCA, hempty⟩ :=
      hp.exists_connected_triple_obstruction
    have hn := h A B C hA hB hC hAB hBC hCA
    simp only [hempty, Set.not_nonempty_empty] at hn

end SimpleGraph
