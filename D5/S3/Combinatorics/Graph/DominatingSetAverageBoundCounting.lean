/- GID: D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting
   mirror-E: none(waiver:finite-counting)
   anchors: []
   utility: none
   digest: Critical dominating vertices satisfy the Beaton–Brown counting identity and private-neighbour bound. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverage
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting

open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph.DominatingSetAverage

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- The members of a dominating set whose deletion destroys domination. -/
noncomputable def criticalVertices (S : Finset V) : Finset V := by
  classical
  exact S.filter fun v => ¬ G.IsDominating (S.erase v : Set V)

/-- Vertices outside a set having exactly one neighbour in the set. -/
noncomputable def privateNeighbors (S : Finset V) : Finset V := by
  classical
  exact univ.filter fun u => u ∉ S ∧ (S.filter (G.Adj u)).card = 1

/-- Critical vertices having a private neighbour outside the set. -/
noncomputable def externallyCritical (S : Finset V) : Finset V := by
  classical
  exact (criticalVertices G S).filter fun v =>
    ∃ u ∈ privateNeighbors G S, G.Adj v u

/-- Deleting a removable member and adding an omitted member count the same edges. -/
theorem removable_pairs_eq_omitted_pairs :
    ((domSets G).sigma fun S =>
      S.filter fun v => G.IsDominating (S.erase v : Set V)).card =
    ((domSets G).sigma fun S => univ \ S).card := by
  classical
  refine Finset.card_bij'
    (fun p _ => ⟨p.1.erase p.2, p.2⟩)
    (fun p _ => ⟨insert p.2 p.1, p.2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    rcases mem_sigma.mp hp with ⟨_, h⟩
    rcases mem_filter.mp h with ⟨_, hd⟩
    exact mem_sigma.mpr ⟨mem_domSets.mpr hd, by simp⟩
  · intro p hp
    rcases mem_sigma.mp hp with ⟨hS, hv⟩
    have hnot : p.2 ∉ p.1 := (mem_sdiff.mp hv).2
    have hd := mem_domSets.mp hS
    refine mem_sigma.mpr ⟨mem_domSets.mpr ?_, mem_filter.mpr ⟨by simp, ?_⟩⟩
    · exact dominating_mono hd (by intro x hx; exact mem_insert_of_mem hx)
    · simpa only [erase_insert hnot] using hd
  · intro p hp
    have hv := (mem_filter.mp (mem_sigma.mp hp).2).1
    cases p
    simp_all
  · intro p hp
    have hv := (mem_sdiff.mp (mem_sigma.mp hp).2).2
    cases p
    simp_all

/-- Beaton–Brown's critical-vertex identity, in subtraction-free natural arithmetic. -/
theorem critical_total_identity :
    (∑ S ∈ domSets G, (criticalVertices G S).card) +
      Fintype.card V * (domSets G).card =
    2 * ∑ S ∈ domSets G, S.card := by
  classical
  have hpair := removable_pairs_eq_omitted_pairs G
  rw [card_sigma, card_sigma] at hpair
  have hc :
      (∑ S ∈ domSets G, (criticalVertices G S).card) +
      (∑ S ∈ domSets G,
        (S.filter fun v => G.IsDominating (S.erase v : Set V)).card) =
      ∑ S ∈ domSets G, S.card := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro S _
    simpa [criticalVertices, Nat.add_comm] using
      S.card_filter_add_card_filter_not
        (fun v => G.IsDominating (S.erase v : Set V))
  have ho :
      (∑ S ∈ domSets G, (univ \ S).card) +
      (∑ S ∈ domSets G, S.card) = Fintype.card V * (domSets G).card := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _S ∈ domSets G, Fintype.card V := by
        apply sum_congr rfl
        intro S _
        simpa using card_sdiff_add_card_eq_card (subset_univ S)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- Beaton–Brown's private-neighbour inequality for each dominating set. -/
theorem externallyCritical_card_le (S : Finset V) :
    (externallyCritical G S).card ≤ (privateNeighbors G S).card := by
  classical
  have hex (v : V) (hv : v ∈ externallyCritical G S) :
      ∃ u ∈ privateNeighbors G S, G.Adj v u :=
    (mem_filter.mp hv).2
  let f (v : V) := if hv : v ∈ externallyCritical G S then (hex v hv).choose else v
  apply Finset.card_le_card_of_injOn f
  · intro v hv
    change f v ∈ privateNeighbors G S
    dsimp only [f]
    split_ifs with h
    · exact (hex v h).choose_spec.1
    · exact (h hv).elim
  · intro v hv w hw heq
    have huv := (hex v hv).choose_spec.2
    have huw := (hex w hw).choose_spec.2
    have hu := (mem_filter.mp (hex v hv).choose_spec.1).2.2
    have hvs := (mem_filter.mp (mem_filter.mp hv).1).1
    have hws := (mem_filter.mp (mem_filter.mp hw).1).1
    have hfv : f v = (hex v hv).choose := by
      dsimp only [f]
      split_ifs with h
      · rfl
      · exact (h hv).elim
    have hfw : f w = (hex w hw).choose := by
      dsimp only [f]
      split_ifs with h
      · rfl
      · exact (h hw).elim
    have hone : (S.filter (G.Adj (f v))).card ≤ 1 := by
      rw [hfv]
      exact Nat.le_of_eq hu
    apply (Finset.card_le_one.mp hone) v (mem_filter.mpr ⟨hvs, by rw [hfv]; exact G.adj_symm huv⟩)
      w (mem_filter.mpr ⟨hws, ?_⟩)
    rw [heq]
    rw [hfw]
    exact G.adj_symm huw

end D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting
