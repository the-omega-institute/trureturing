import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskGraph

/-! The square law for contact coordinates closes a triangle of cubic vertices. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicMaskTriangle

open Finset
open Q9TenMaskGraph (SquareCompletion)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem neighbors_eq_triple {x a b c : V}
    (hx : G.degree x = 3) (ha : G.Adj x a) (hb : G.Adj x b) (hc : G.Adj x c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.neighborFinset x = {a, b, c} := by
  symm
  apply eq_of_subset_of_card_le
  · intro y hy
    simp only [mem_insert, mem_singleton] at hy
    apply (G.mem_neighborFinset x y).mpr
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  · rw [SimpleGraph.card_neighborFinset_eq_degree, hx]
    rw [card_insert_of_notMem, card_pair hbc]
    simpa [mem_insert, mem_singleton] using (not_or.mpr ⟨hab, hac⟩)

/-- The three cubic vertices in a triangle have the same fourth neighbor.
If that neighbor is also cubic, the clique forms a component. -/
theorem triangle_closes
    (hSquare : SquareCompletion G) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (ha : G.degree a = 3) (hb : G.degree b = 3) (hc : G.degree c = 3) :
    ∃ d, G.Adj a d ∧ G.Adj b d ∧ G.Adj c d ∧
      (G.degree d = 3 →
        ∀ x ∈ ({a, b, c, d} : Finset V), G.neighborFinset x ⊆ {a, b, c, d}) := by
  have hab' := G.ne_of_adj hab
  have hbc' := G.ne_of_adj hbc
  have hca' := G.ne_of_adj hca
  obtain ⟨d, hdb, hcd, had⟩ :=
    hSquare (a := b) (v := c) (c := a) hbc hab.symm hca' hb hc
  have hcd' := G.ne_of_adj hcd
  have had' := G.ne_of_adj had
  have hNC := neighbors_eq_triple hc hca hbc.symm hcd hab' had' hdb.symm
  obtain ⟨e, hea, hbe, hce⟩ :=
    hSquare (a := a) (v := b) (c := c) hab hca.symm hbc' ha hb
  have he : e = d := by
    have h : e ∈ ({a, b, d} : Finset V) := by
      rw [← hNC]
      exact (G.mem_neighborFinset c e).mpr hce
    simpa [hea, (G.ne_of_adj hbe).symm] using h
  have hbd : G.Adj b d := he ▸ hbe
  refine ⟨d, had, hbd, hcd, fun hd x hx => ?_⟩
  have hNA := neighbors_eq_triple ha hab hca.symm had hbc' hdb.symm hcd'
  have hNB := neighbors_eq_triple hb hab.symm hbc hbd hca'.symm had' hcd'
  have hND := neighbors_eq_triple hd had.symm hbd.symm hcd.symm hab' hca'.symm hbc'
  have hcases : x = a ∨ x = b ∨ x = c ∨ x = d := by simpa using hx
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [hNA]
    intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl | rfl <;> simp
  · rw [hNB]
    intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl | rfl <;> simp
  · rw [hNC]
    intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl | rfl <;> simp
  · rw [hND]
    intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl | rfl <;> simp

#print axioms triangle_closes

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicMaskTriangle
