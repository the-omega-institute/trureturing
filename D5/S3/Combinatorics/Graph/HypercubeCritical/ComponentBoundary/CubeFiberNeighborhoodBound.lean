/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CubeFiberNeighborhoodBound
   generality: G
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Neighbouring pattern fibres bound the size of the closed neighbourhood. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeClosedNeighborhoodRecurrence

/-! A split into pattern and residual coordinates bounds the closed neighbourhood from the
sizes of the fibres alone. Each pattern contributes the maximum of its own recurrence bound
and the sizes of the fibres at its one-flip neighbours. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeFiberNeighborhoodBound

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (flip flip_adj)
open CubeClosedNeighborhoodRecurrence (closedNeighborhood h h_le_closedNeighborhood_card)

private theorem mem_neighborhood_fiber {k n : ℕ}
    (S : Finset ((Fin k → Bool) × (Fin n → Bool))) (p : Fin k → Bool) (y : Fin n → Bool) :
    Fin.append p y ∈ closedNeighborhood (S.map (Fin.appendEquiv k n).toEmbedding) ↔
      y ∈ closedNeighborhood (univ.filter fun z => (p, z) ∈ S) ∨
        ∃ q : Fin k → Bool, hammingDist p q = 1 ∧ (q, y) ∈ S := by
  have distance (q : Fin k → Bool) (z : Fin n → Bool) :
      hammingDist (Fin.append p y) (Fin.append q z) = hammingDist p q + hammingDist y z := by
    simp only [hammingDist, card_eq_sum_ones, sum_filter, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right]
  simp only [closedNeighborhood, mem_filter, mem_univ, true_and, mem_map]
  constructor
  · rintro ⟨_, ⟨⟨q, z⟩, hqz, rfl⟩, hd⟩
    change hammingDist (Fin.append p y) (Fin.append q z) ≤ 1 at hd
    rw [distance] at hd
    by_cases hpq : hammingDist p q = 0
    · obtain rfl := hammingDist_eq_zero.mp hpq
      exact Or.inl ⟨z, hqz, by omega⟩
    · have hyz : y = z := hammingDist_eq_zero.mp (by omega)
      exact Or.inr ⟨q, by omega, hyz.symm ▸ hqz⟩
  · rintro (⟨z, hz, hd⟩ | ⟨q, hq, hqy⟩)
    · exact ⟨Fin.append p z, ⟨(p, z), hz, rfl⟩, by simpa only [distance,
        hammingDist_self, zero_add] using hd⟩
    · exact ⟨Fin.append q y, ⟨(q, y), hqy, rfl⟩, by simp [distance, hq]⟩

private theorem sum_card_fibers {k n : ℕ} (T : Finset (Fin (k + n) → Bool)) :
    (∑ p : Fin k → Bool, (univ.filter fun y : Fin n → Bool => Fin.append p y ∈ T).card) =
      T.card := by
  calc
    _ = ∑ v : (Fin k → Bool) × (Fin n → Bool),
          if Fin.appendEquiv k n v ∈ T then 1 else 0 := by
        rw [Fintype.sum_prod_type]
        simp only [card_eq_sum_ones, sum_filter]
        rfl
    _ = ∑ x : Fin (k + n) → Bool, if x ∈ T then 1 else 0 :=
      (Fin.appendEquiv k n).sum_comp (fun x => if x ∈ T then (1 : ℕ) else 0)
    _ = T.card := by
      rw [card_eq_sum_ones T, ← sum_filter]
      simp

/-- In product coordinates each closed-neighbourhood fibre contains the closed neighbourhood
of its own fibre and every fibre reached by toggling a pattern coordinate. The supremum over
the pattern coordinates is zero when there are no such coordinates. -/
theorem sum_max_le_closedNeighborhood_card {k n : ℕ}
    (S : Finset ((Fin k → Bool) × (Fin n → Bool))) :
    let F := fun p : Fin k → Bool => univ.filter fun y : Fin n → Bool => (p, y) ∈ S
    (∑ p : Fin k → Bool, max (h n (F p).card)
      ((univ : Finset (Fin k)).sup fun i => (F (flip p i)).card)) ≤
      (closedNeighborhood (S.map (Fin.appendEquiv k n).toEmbedding)).card := by
  dsimp only
  rw [← sum_card_fibers]
  apply sum_le_sum
  intro p _
  apply max_le
  · refine (h_le_closedNeighborhood_card _).trans (card_le_card ?_)
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, (mem_neighborhood_fiber S p y).mpr (Or.inl hy)⟩
  · apply Finset.sup_le_iff.mpr
    intro i _
    apply card_le_card
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, (mem_neighborhood_fiber S p y).mpr
      (Or.inr ⟨flip p i, flip_adj p i, (mem_filter.mp hy).2⟩)⟩

#print axioms sum_max_le_closedNeighborhood_card

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeFiberNeighborhoodBound
