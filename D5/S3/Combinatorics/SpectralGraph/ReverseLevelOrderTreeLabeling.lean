/- GID: D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reverse level order labels give exactly one nonzero entry in each column tail. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! Column tails of tree adjacency matrices under reverse level order labelings. -/

namespace D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling

/-- Labels `0, …, n - 1` represent the source's labels `1, …, n`. -/
def claim : Prop :=
  ∀ (n : ℕ) (g : SimpleGraph (Fin n)) [DecidableRel g.Adj],
    g.IsTree → ∀ (r : Fin n) (l : Fin n ≃ Fin n),
      @StrictAnti (Fin n) (Fin n) (Preorder.lift (g.dist r)) inferInstance l →
      ∀ i : Fin n, i.val + 1 < n →
        ∃! j : Fin n, i < j ∧ g.adjMatrix ℕ (l.symm j) (l.symm i) ≠ 0

private lemma unique_parent {n : ℕ} {g : SimpleGraph (Fin n)} (ht : g.IsTree)
    (r v : Fin n) (hv : v ≠ r) :
    ∃! w, g.Adj v w ∧ g.dist r w + 1 = g.dist r v := by
  obtain ⟨p, hp⟩ := ht.connected.exists_walk_length_eq_dist v r
  obtain ⟨w, ha, q, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hv p
  have hq : g.dist r w ≤ q.length := by
    rw [SimpleGraph.dist_comm]
    exact SimpleGraph.dist_le q
  have hlen : q.length + 1 = g.dist r v := by
    calc
      q.length + 1 = g.dist v r := hp
      _ = g.dist r v := SimpleGraph.dist_comm
  have hw : g.dist r w + 1 = g.dist r v := by
    rcases ht.dist_eq_dist_add_one_of_adj r ha with h | h <;> omega
  refine ⟨w, ⟨ha, hw⟩, ?_⟩
  intro u hu
  obtain ⟨s, hs⟩ := ht.connected.exists_walk_length_eq_dist u r
  have hslen : (s.cons hu.1).length = g.dist v r := by
    rw [SimpleGraph.Walk.length_cons, hs, SimpleGraph.dist_comm,
      hu.2, SimpleGraph.dist_comm]
  have he : s.cons hu.1 = q.cons ha :=
    (ht.existsUnique_path v r).unique
      ((s.cons hu.1).isPath_of_length_eq_dist hslen)
      ((q.cons ha).isPath_of_length_eq_dist hp)
  have hevert := congrArg (fun t : g.Walk v r => t.getVert 1) he
  simpa only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero] using hevert

private lemma larger_label_iff_parent {n : ℕ} {g : SimpleGraph (Fin n)}
    (ht : g.IsTree) {r : Fin n} {l : Fin n ≃ Fin n}
    (hl : @StrictAnti (Fin n) (Fin n) (Preorder.lift (g.dist r)) inferInstance l)
    {v w : Fin n} (ha : g.Adj v w) :
    l v < l w ↔ g.dist r w + 1 = g.dist r v := by
  constructor
  · intro h
    rcases ht.dist_eq_dist_add_one_of_adj r ha with hp | hc
    · exact hp.symm
    · exact (lt_asymm h (hl (a := v) (b := w) (by
        change g.dist r v < g.dist r w
        omega))).elim
  · intro hp
    exact hl (a := w) (b := v) (by
      change g.dist r w < g.dist r v
      omega)

private lemma column_vertex_ne_root {n : ℕ} {g : SimpleGraph (Fin n)}
    (ht : g.IsTree) {r : Fin n} {l : Fin n ≃ Fin n}
    (hl : @StrictAnti (Fin n) (Fin n) (Preorder.lift (g.dist r)) inferInstance l)
    (i : Fin n) (hi : i.val + 1 < n) :
    l.symm i ≠ r := by
  intro h
  let j : Fin n := ⟨i.val + 1, hi⟩
  have hj : l.symm j ≠ r := by
    intro hj
    have he : j = i := l.symm.injective (hj.trans h.symm)
    have heval := congrArg Fin.val he
    dsimp [j] at heval
    omega
  have hd : g.dist r r < g.dist r (l.symm j) := by
    rw [SimpleGraph.dist_self]
    exact ht.connected.pos_dist_of_ne hj.symm
  have hlt := hl (a := r) (b := l.symm j) hd
  rw [l.apply_symm_apply, ← h, l.apply_symm_apply] at hlt
  have hval : j.val < i.val := hlt
  dsimp [j] at hval
  omega

private lemma column_tail_unique {n : ℕ} {g : SimpleGraph (Fin n)}
    [DecidableRel g.Adj] (ht : g.IsTree) {r : Fin n} {l : Fin n ≃ Fin n}
    (hl : @StrictAnti (Fin n) (Fin n) (Preorder.lift (g.dist r)) inferInstance l)
    (i : Fin n) (hv : l.symm i ≠ r) :
    ∃! j : Fin n, i < j ∧ g.adjMatrix ℕ (l.symm j) (l.symm i) ≠ 0 := by
  obtain ⟨w, hw, hu⟩ := unique_parent ht r (l.symm i) hv
  have hlabel : i < l w := by
    have h := (larger_label_iff_parent ht hl hw.1).mpr hw.2
    rwa [l.apply_symm_apply] at h
  refine ⟨l w, ⟨hlabel, ?_⟩, ?_⟩
  · rw [l.symm_apply_apply, SimpleGraph.adjMatrix_apply, ite_eq_left hw.1.symm]
    exact Nat.one_ne_zero
  · intro j hj
    have ha : g.Adj (l.symm i) (l.symm j) := by
      by_contra hn
      have hn' : ¬ g.Adj (l.symm j) (l.symm i) := fun h => hn h.symm
      rw [SimpleGraph.adjMatrix_apply, ite_eq_right hn'] at hj
      exact hj.2 rfl
    have hp := (larger_label_iff_parent ht hl ha).mp (by
      simpa only [l.apply_symm_apply] using hj.1)
    have he := hu (l.symm j) ⟨ha, hp⟩
    simpa only [l.apply_symm_apply] using congrArg l he

theorem result : claim := by
  intro n g _ ht r l hl i hi
  exact column_tail_unique ht hl i (column_vertex_ne_root ht hl i hi)

end D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling
