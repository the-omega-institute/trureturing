import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenMaskGraph
import Mathlib.Data.Fin.Tuple.Sort

/-! A degree partition and the coordinate action sorting cubic vertices by their
incidence with the high-degree vertices. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskNineAxisProfile

open Finset
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V]

/-- The sum of the excess degrees is exactly three. -/
theorem excess_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 9) (hE : G.edgeFinset.card = 15)
    (hmin : ∀ v, 3 ≤ G.degree v) :
    (∑ v : V, (G.degree v - 3)) = 3 := by
  have hs : (∑ v : V, G.degree v) = 30 := by
    rw [G.sum_degrees_eq_twice_card_edges, hE]
  have he (v : V) : G.degree v = 3 + (G.degree v - 3) := by
    have h := hmin v
    omega
  have hc : (∑ _ : V, (3 : ℕ)) = 27 := by
    simp [hV]
  have hh : (∑ v : V, G.degree v) = 27 + ∑ v : V, (G.degree v - 3) := by
    rw [← hc, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => he v
  rw [hs] at hh
  omega

/-- Split the vertices according to their degree. Relabel the high-degree
vertices by their degrees and the cubic vertices by their binary incidence
with that first block. The permutations used in the two sorts preserve the
entire graph up to isomorphism. -/
theorem sorted_degree_blocks (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 9) (hE : G.edgeFinset.card = 15)
    (hmin : ∀ v, 3 ≤ G.degree v) :
    ∃ h l : ℕ, ∃ e : Fin h ⊕ Fin l ≃ V,
      0 < h ∧ h ≤ 3 ∧ h + l = 9 ∧
      (∀ i, 3 < G.degree (e (Sum.inl i))) ∧
      (∀ j, G.degree (e (Sum.inr j)) = 3) ∧
      Monotone (fun i => G.degree (e (Sum.inl i))) ∧
      Monotone (fun j => ∑ i : Fin h, if G.Adj (e (Sum.inl i)) (e (Sum.inr j))
        then 2 ^ i.val else 0) := by
  classical
  let H := univ.filter (fun v : V => 3 < G.degree v)
  let P : V → Prop := fun v => 3 < G.degree v
  let a := Fintype.card {v : V // P v}
  let b := Fintype.card {v : V // ¬ P v}
  have hH : H.card = a := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun v => by simp [H, P])
  have hsum := excess_sum G hV hE hmin
  have hsumH : (∑ v ∈ H, (G.degree v - 3)) = 3 := by
    calc
      _ = ∑ v : V, (G.degree v - 3) := by
        refine sum_subset (subset_univ H) ?_
        intro v _ hv
        have hn : ¬ 3 < G.degree v := fun he => hv (mem_filter.mpr ⟨mem_univ _, he⟩)
        exact Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hn)
      _ = 3 := hsum
  have haPos : 0 < a := by
    by_contra! hn
    have hz : H.card = 0 := by omega
    rw [card_eq_zero.mp hz, sum_empty] at hsumH
    omega
  have haMax : a ≤ 3 := by
    have hle : ∑ _ ∈ H, (1 : ℕ) ≤ ∑ v ∈ H, (G.degree v - 3) :=
      sum_le_sum fun v hv => by
        have hd : 3 < G.degree v := (mem_filter.mp hv).2
        omega
    simpa [hH, hsumH] using hle
  let eH : Fin a ≃ {v : V // P v} := Fintype.equivOfCardEq (by simp [a])
  let eL : Fin b ≃ {v : V // ¬P v} := Fintype.equivOfCardEq (by simp [b])
  let d : Fin a → ℕ := fun i => G.degree (eH i).val
  let high := (Tuple.sort d).trans eH
  let sig : Fin b → ℕ := fun j => ∑ i : Fin a,
    if G.Adj (high i).val (eL j).val then 2 ^ i.val else 0
  let low := (Tuple.sort sig).trans eL
  let e := (Equiv.sumCongr high low).trans (Equiv.sumCompl P)
  have hab : a + b = 9 := by
    have hc := Fintype.card_congr e
    simpa [hV] using hc
  refine ⟨a,b,e,haPos,haMax,hab,?_,?_,?_,?_⟩
  · intro i
    exact (high i).property
  · intro j
    have hl := (low j).property
    have hm := hmin (low j).val
    change G.degree (low j).val = 3
    dsimp [P] at hl
    omega
  · exact Tuple.monotone_sort d
  · exact Tuple.monotone_sort sig

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskNineAxisProfile
