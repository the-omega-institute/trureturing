import D5.S3.Combinatorics.Graph.Incidence.UnsignedStarTorsion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.Graph.Incidence.UnsignedStarTorsion
open scoped BigOperators

/- Transient exact inference: original units/differences and actual original-H
coefficients. This file is build evidence, not a retained declaration/module. -/
example {V X H : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
    [Fintype H] (g : Edges V X)
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hrobust : ∀ D : Finset X, D.card ≤ 2 →
      ¬ (g.graphAfterDeleting (D : Set X)).IsBipartite)
    (rows : H → X → ℤ) (d : H → V → ℤ) (c : V → H → ℤ)
    (hd : ∀ T, g.starMap (d T) = rows T)
    (hcert : ∀ v i, g.starRow v i = ∑ T, c v T * rows T i)
    (P : X → ℤ)
    (hP : (∃ i, P = fun t => if t = i then 1 else 0) ∨
      ∃ i j, i ≠ j ∧ P = fun t =>
        (if t = i then 1 else 0) - (if t = j then 1 else 0))
    (k : ℕ) (hk : 0 < k) (h : H → ℤ)
    (hmult : ∀ i, (k : ℤ) * P i = ∑ T, h T * rows T i) :
    ∃ b : V → ℤ, ∀ i, P i = ∑ T, (∑ v, b v * c v T) * rows T i := by
  classical
  have hs : (Finset.univ.filter (fun i => P i ≠ 0)).card ≤ 2 := by
    rcases hP with ⟨i, rfl⟩ | ⟨i, j, _, rfl⟩
    · have hsub : Finset.univ.filter (fun t : X => (if t = i then (1 : ℤ) else 0) ≠ 0)
          ⊆ {i} := by
        intro t ht
        by_cases he : t = i
        · simp [he]
        · simpa [he] using (Finset.mem_filter.mp ht).2
      exact (Finset.card_le_card hsub).trans (by simp)
    · have hsub : Finset.univ.filter (fun t : X =>
          ((if t = i then (1 : ℤ) else 0) - (if t = j then 1 else 0)) ≠ 0)
          ⊆ {i, j} := by
        intro t ht
        by_cases hi : t = i
        · simp [hi]
        by_cases hj : t = j
        · simp [hj]
        · simpa [hi, hj] using (Finset.mem_filter.mp ht).2
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  obtain ⟨b, _, hb⟩ := g.source_coefficients_of_sparse_multiple hc 2 hrobust
    rows d c hd hcert k hk P hs h hmult
  exact ⟨b, hb⟩
