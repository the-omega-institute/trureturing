/- GID: D5/S3/Combinatorics/Graph/DemandColoring/BipartiteDemandColoring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DemandColoring/BipartiteDemandColoring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact natural demands on a two-colored graph share one finite palette. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring

/-- A total two-coloring allocates exact demands in one common palette. Each layer is
independent; isolated vertices and the empty palette require only the vertex capacity. -/
theorem exists_independent_layers {V : Type*} (G : SimpleGraph V)
    (b : G.Coloring Bool) (k : ℕ) (z : V → ℕ)
    (hv : ∀ v, z v ≤ k)
    (he : ∀ ⦃u v⦄, G.Adj u v → z u + z v ≤ k) :
    ∃ W : Fin k → V → Bool,
      (∀ c, G.IsIndepSet {v | W c v = true}) ∧
      ∀ v, (Finset.univ.filter (fun c => W c v = true)).card = z v := by
  let W : Fin k → V → Bool := fun c v =>
    if b v then decide (c.val < z v) else decide (k - z v ≤ c.val)
  refine ⟨W, ?_, ?_⟩
  · intro c u hu v hv' _ huv
    have different := b.valid huv
    have capacity := he huv
    have zu := hv u
    have zv := hv v
    cases bu : b u <;> cases bv : b v <;>
      simp only [bu, bv, ne_eq, not_true_eq_false] at different
    · simp [W, bu] at hu
      simp [W, bv] at hv'
      omega
    · simp [W, bu] at hu
      simp [W, bv] at hv'
      omega
  · intro v
    cases bv : b v
    · have count := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin k))) (fun c => c.val < k - z v)
      have prefix : (Finset.univ.filter (fun c : Fin k => c.val < k - z v)).card =
          k - z v := by
        simpa only [Nat.min_eq_right (Nat.sub_le k (z v))] using
          (Fin.card_filter_val_lt (n := k) (m := k - z v))
      have complement : (Finset.univ.filter (fun c : Fin k => k - z v ≤ c.val)).card =
          z v := by
        simp only [not_lt] at count
        rw [prefix] at count
        simp only [Finset.card_univ, Fintype.card_fin] at count
        have := hv v
        omega
      simpa [W, bv] using complement
    · simpa [W, bv, Nat.min_eq_right (hv v)] using
        (Fin.card_filter_val_lt (n := k) (m := z v))

end D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring
