/- GID: D5/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ReverseLevelOrderTreeLabeling
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reverse level order labels give exactly one nonzero entry in each column tail. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

namespace D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling

/-- Labels `0, …, n - 1` represent the source's labels `1, …, n`. -/
def IsReverseLevelOrder {n : ℕ} (g : SimpleGraph (Fin n)) (r : Fin n)
    (l : Fin n ≃ Fin n) : Prop :=
  ∀ u v, g.dist r u < g.dist r v → l v < l u

def claim : Prop :=
  ∀ (n : ℕ) (g : SimpleGraph (Fin n)) [DecidableRel g.Adj],
    g.IsTree → ∀ (r : Fin n) (l : Fin n ≃ Fin n), IsReverseLevelOrder g r l →
      ∀ i : Fin n, i.val + 1 < n →
        ∃! j : Fin n, i < j ∧ g.adjMatrix ℕ (l.symm j) (l.symm i) ≠ 0

private lemma unique_parent {n : ℕ} {g : SimpleGraph (Fin n)} (ht : g.IsTree)
    (r v : Fin n) (hv : v ≠ r) :
    ∃! w, g.Adj v w ∧ g.dist r w + 1 = g.dist r v := by
  sorry

private lemma larger_label_iff_parent {n : ℕ} {g : SimpleGraph (Fin n)}
    (ht : g.IsTree) {r : Fin n} {l : Fin n ≃ Fin n}
    (hl : IsReverseLevelOrder g r l) {v w : Fin n} (ha : g.Adj v w) :
    l v < l w ↔ g.dist r w + 1 = g.dist r v := by
  sorry

private lemma column_vertex_ne_root {n : ℕ} {g : SimpleGraph (Fin n)}
    (ht : g.IsTree) {r : Fin n} {l : Fin n ≃ Fin n}
    (hl : IsReverseLevelOrder g r l) (i : Fin n) (hi : i.val + 1 < n) :
    l.symm i ≠ r := by
  sorry

private lemma column_tail_unique {n : ℕ} {g : SimpleGraph (Fin n)}
    [DecidableRel g.Adj] (ht : g.IsTree) {r : Fin n} {l : Fin n ≃ Fin n}
    (hl : IsReverseLevelOrder g r l) (i : Fin n) (hv : l.symm i ≠ r) :
    ∃! j : Fin n, i < j ∧ g.adjMatrix ℕ (l.symm j) (l.symm i) ≠ 0 := by
  sorry

theorem result : claim := by
  intro n g _ ht r l hl i hi
  exact column_tail_unique ht hl i (column_vertex_ne_root ht hl i hi)

end D5.S3.Combinatorics.SpectralGraph.ReverseLevelOrderTreeLabeling
