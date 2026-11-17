/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoLocal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Derive the local and weighted incidence identities directly from the original symmetric slice parameters and girth. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
import Batteries.Tactic.OpenPrivate

/-! Actual local identities and weighted incidence counts for the symmetric slice. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
open scoped BigOperators

attribute [local instance] Classical.propDecidable

open private rootThreeWeight root_three_paths_card root_weight_low root_weight_high
  low_vertex_high_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity

open private threePaths onePaths sum_degree_parts neighbor_parts_card
  one_three_paths_card_le_rectangle one_paths_card_eq_three_mul sum_high_neighbors
  degree_parts_union degree_parts_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem degree_three_root_identity
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    {x : V} (hx : G.degree x = 3) :
    (threePaths G {x}).card + (degreeThree G (G.neighborFinset x)).card =
      6 + ∑ y ∈ degreeThree G (G.neighborFinset x),
        (degreeThree G (G.neighborFinset y)).card := by
  have hroot := root_three_paths_card (G := G) x
  have hsplit := sum_degree_parts hdeg (G.neighborFinset x) (rootThreeWeight G x)
  have hlowSum :
      (∑ y ∈ degreeTwo G (G.neighborFinset x), rootThreeWeight G x y) =
        2 * (degreeTwo G (G.neighborFinset x)).card := by
    calc
      _ = ∑ _y ∈ degreeTwo G (G.neighborFinset x), 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hm := Finset.mem_filter.mp hy
        exact root_weight_low hdeg hlow hx
          ((G.mem_neighborFinset _ _).mp hm.1) hm.2
      _ = _ := by simp [Nat.mul_comm]
  have hhighSum :
      (∑ y ∈ degreeThree G (G.neighborFinset x), rootThreeWeight G x y) =
        (degreeThree G (G.neighborFinset x)).card +
          ∑ y ∈ degreeThree G (G.neighborFinset x),
            (degreeThree G (G.neighborFinset y)).card := by
    calc
      _ = ∑ y ∈ degreeThree G (G.neighborFinset x),
          (1 + (degreeThree G (G.neighborFinset y)).card) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hm := Finset.mem_filter.mp hy
        exact root_weight_high hdeg hx
          ((G.mem_neighborFinset _ _).mp hm.1) hm.2
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hparts := neighbor_parts_card hdeg x
  rw [hx] at hparts
  omega

private theorem degree_three_local_bound
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (hR : R.card = 11)
    {x : V} (hxL : x ∈ L) (hx : G.degree x = 3) :
    (∑ y ∈ degreeThree G (G.neighborFinset x),
        (degreeThree G (G.neighborFinset y)).card) ≤
      (degreeThree G (G.neighborFinset x)).card + 2 := by
  have hroots : ({x} : Finset V) ⊆ L := by simpa using hxL
  have hu := one_three_paths_card_le_rectangle {x} hroots hpart hg
  rw [one_paths_card_eq_three_mul _ (by simpa using hx)] at hu
  simp only [Finset.card_singleton, mul_one, one_mul] at hu
  rw [hR] at hu
  have hi := degree_three_root_identity hdeg hlow hx
  omega

private theorem side_high_neighbor_sum
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False) :
    (∑ y ∈ degreeThree G R, (degreeThree G (G.neighborFinset y)).card) +
        2 * (degreeTwo G R).card = 3 * (degreeThree G L).card := by
  have htotal := sum_high_neighbors hpart
  have hsplit := sum_degree_parts hdeg R
    (fun y => (degreeThree G (G.neighborFinset y)).card)
  have hlowSum :
      (∑ y ∈ degreeTwo G R, (degreeThree G (G.neighborFinset y)).card) =
        2 * (degreeTwo G R).card := by
    calc
      _ = ∑ _y ∈ degreeTwo G R, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact low_vertex_high_neighbor_card hdeg hlow (Finset.mem_filter.mp hy).2
      _ = _ := by simp [Nat.mul_comm]
  omega

private theorem symmetric_high_counts
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4) :
    (degreeThree G L).card = 7 ∧ (degreeThree G R).card = 7 ∧
      (∑ x ∈ degreeThree G L, (degreeThree G (G.neighborFinset x)).card) = 13 ∧
      (∑ y ∈ degreeThree G R, (degreeThree G (G.neighborFinset y)).card) = 13 := by
  have hleft := congrArg Finset.card (degree_parts_union hdeg L)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint L)] at hleft
  have hright := congrArg Finset.card (degree_parts_union hdeg R)
  rw [Finset.card_union_of_disjoint (degree_parts_disjoint R)] at hright
  have hL3 : (degreeThree G L).card = 7 := by omega
  have hR3 : (degreeThree G R).card = 7 := by omega
  have hsumR := side_high_neighbor_sum hpart hdeg hlow
  have hsumL := side_high_neighbor_sum hpart.symm hdeg hlow
  refine ⟨hL3, hR3, ?_, ?_⟩ <;> omega

private theorem high_neighbors_eq_filter
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {x : V} (hxL : x ∈ L) :
    degreeThree G (G.neighborFinset x) =
      (degreeThree G R).filter (fun y => G.Adj x y) := by
  ext y
  simp only [degreeThree, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hxy, hy3⟩
    exact ⟨⟨hpart.mem_of_mem_adj hxL hxy, hy3⟩, hxy⟩
  · rintro ⟨⟨_, hy3⟩, hxy⟩
    exact ⟨hxy, hy3⟩

private theorem high_neighbor_weighted_double_count
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V)) :
    (∑ x ∈ degreeThree G L, ∑ y ∈ degreeThree G (G.neighborFinset x),
        (degreeThree G (G.neighborFinset y)).card) =
      ∑ y ∈ degreeThree G R, ((degreeThree G (G.neighborFinset y)).card) ^ 2 := by
  calc
    _ = ∑ x ∈ degreeThree G L, ∑ y ∈ degreeThree G R,
        if G.Adj x y then (degreeThree G (G.neighborFinset y)).card else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [high_neighbors_eq_filter hpart (Finset.mem_filter.mp hx).1,
        Finset.sum_filter]
    _ = ∑ y ∈ degreeThree G R, ∑ x ∈ degreeThree G L,
        if G.Adj x y then (degreeThree G (G.neighborFinset y)).card else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      have hfilter :
          (degreeThree G L).filter (fun x => G.Adj x y) =
            degreeThree G (G.neighborFinset y) := by
        rw [high_neighbors_eq_filter hpart.symm (Finset.mem_filter.mp hy).1]
        apply Finset.filter_congr
        intro x hx
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      calc
        _ = ∑ _x ∈ (degreeThree G L).filter (fun x => G.Adj x y),
            (degreeThree G (G.neighborFinset y)).card := by
          rw [Finset.sum_filter]
        _ = _ := by rw [hfilter]; simp [pow_two, Nat.mul_comm]

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal
