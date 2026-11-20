/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q6EvenResidualNeighborhood
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q6EvenResidualNeighborhood
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Parity-balanced residual sets with even neighborhood counts bound six-cube fiber capacities. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

/-! The even-neighborhood constraint and the resulting packing bound for actual fibers. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q6EvenResidualNeighborhood

open scoped Classical BigOperators
open Finset
open Hypercube (hypercube hypercube_regular)
open BalancedCriticalSpectrum (Q flip flip_adj)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private diff diff_flip diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

local notation "A" => SimpleGraph.Adj (hypercube 6)
local notation "N" => SimpleGraph.neighborFinset (hypercube 6)

private theorem mem_neighbors {x z : Q 6} : z ∈ N x ↔ A x z := by simp

private theorem card_neighbors (x : Q 6) : (N x).card = 6 := by
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact (hypercube_regular 6).degree_eq x

private theorem common_neighbors_card (x y : Q 6) (hxy : x ≠ y)
    (hne : ((N x).filter (A y)).Nonempty) :
    ((N x).filter (A y)).card = 2 := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨i, rfl⟩ := adjacent_exists_flip
    (mem_neighbors.mp (mem_filter.mp hw).1)
  have hdist := (diff_of_adj_flip hxy i (mem_filter.mp hw).2.symm).2
  have heq : (N x).filter (A y) = (diff x y).image (flip x) := by
    ext z
    simp only [mem_filter, mem_neighbors, mem_image]
    constructor
    · rintro ⟨hxz, hyz⟩
      obtain ⟨j, rfl⟩ := adjacent_exists_flip hxz
      exact ⟨j, (diff_of_adj_flip hxy j hyz.symm).1, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨flip_adj x j, (show A (flip x j) y from ?_).symm⟩
      change (diff (flip x j) y).card = 1
      have hc := card_erase_add_one hj
      rw [diff_flip, ite_eq_left hj]
      omega
  rw [heq, card_image_of_injective _ (flip_injective x), hdist]

private theorem common_neighbors_even (x y : Q 6) : Even ((N x).filter (A y)).card := by
  by_cases hxy : x = y
  · subst y
    have h : (N x).filter (A x) = N x :=
      filter_eq_self.mpr fun _ hz => mem_neighbors.mp hz
    rw [h, card_neighbors]
    decide
  · by_cases hne : ((N x).filter (A y)).Nonempty
    · rw [common_neighbors_card x y hxy hne]
      decide
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]
      decide

/-- Every neighborhood meets the complement of an eight-per-side residual set whose
neighborhood counts are even at every vertex of the six-cube. -/
theorem exists_neighbor_not_mem_residual {R : Finset (Q 6)}
    (hSides : ∀ b : Bool, (R.filter fun x => cubeParity x = b).card = 8)
    (hEven : ∀ x : Q 6, Even (R.filter (A x)).card)
    (y : Q 6) : ∃ z, A y z ∧ z ∉ R := by
  by_contra h
  let H := R.filter fun x => cubeParity x = !cubeParity y
  have hOpp {x z : Q 6} (hxz : A x z) : cubeParity z = !cubeParity x :=
    (Bool.not_eq_iff.mpr (cubeParity_ne_of_adj hxz)).symm
  have hsub : N y ⊆ H := by
    intro z hz
    have hyz := mem_neighbors.mp hz
    exact mem_filter.mpr ⟨Classical.byContradiction fun hzR => h ⟨z, hyz, hzR⟩, hOpp hyz⟩
  have hcard := card_sdiff_add_card_eq_card hsub
  have hH : H.card = 8 := hSides _
  rw [card_neighbors, hH] at hcard
  obtain ⟨a, b, hab, hpair⟩ := card_eq_two.mp (by omega : (H \ N y).card = 2)
  have hsplit : {a, b} ∪ N y = H := by
    rw [← hpair, sdiff_union_of_subset hsub]
  have haH : a ∈ H := by rw [← hsplit]; simp
  have hdisj : Disjoint ({a, b} : Finset (Q 6)) (N y) := by
    rw [← hpair]
    exact disjoint_sdiff_self_left
  have hsame : N a ⊆ N b := by
    intro z hz
    have haz := mem_neighbors.mp hz
    have hParity : (!cubeParity z) = !cubeParity y :=
      (hOpp haz.symm).symm.trans (mem_filter.mp haH).2
    have hfilter : R.filter (A z) = H.filter (A z) := by
      ext w
      simp only [H, mem_filter]
      exact ⟨fun ⟨hw, hzw⟩ => ⟨⟨hw, (hOpp hzw).trans hParity⟩, hzw⟩,
        fun ⟨⟨hw, _⟩, hzw⟩ => ⟨hw, hzw⟩⟩
    have he := hEven z
    rw [hfilter, ← hsplit, filter_union,
      card_union_of_disjoint (hdisj.mono (filter_subset _ _) (filter_subset _ _))] at he
    by_contra hzb
    have hnot : ¬ A z b := fun hzb' => hzb (mem_neighbors.mpr hzb'.symm)
    have hsingle : ({a, b} : Finset (Q 6)).filter (A z) = {a} := by
      simp [filter_insert, filter_singleton, haz.symm, hnot]
    rw [hsingle, card_singleton] at he
    obtain ⟨k, hk⟩ := common_neighbors_even y z
    obtain ⟨j, hj⟩ := he
    omega
  have hall : (N a).filter (A b) = N a :=
    filter_eq_self.mpr fun _ hz => mem_neighbors.mp (hsame hz)
  have hne : ((N a).filter (A b)).Nonempty := by
    rw [hall, ← card_pos, card_neighbors]
    decide
  have hc := common_neighbors_card a b hab hne
  rw [hall, card_neighbors] at hc
  omega

/-- Four occupied positions per occupied fiber and their exclusion from adjacent
residual fibers bound the total number of actual vertices in the product cube. -/
theorem card_le_256_of_residual_fibers {R : Finset (Q 6)}
    (hSides : ∀ b : Bool, (R.filter fun x => cubeParity x = b).card = 8)
    (hEven : ∀ x : Q 6, Even (R.filter (A x)).card)
    (U : Finset (Q 3 × Q 6)) (S : Q 6 → Finset (Q 3))
    (hCard : ∀ z ∉ R, (S z).card = 4)
    (hOccupied : ∀ z ∉ R, ∀ p, (p, z) ∈ U → p ∈ S z)
    (hSeparated : ∀ y ∈ R, ∀ z ∉ R, A y z → ∀ p ∈ S z, (p, y) ∉ U) :
    U.card ≤ 256 := by
  let fiber (y : Q 6) := (univ : Finset (Q 3)).filter fun p => (p, y) ∈ U
  have hBound (y : Q 6) : (fiber y).card ≤ 4 := by
    by_cases hy : y ∈ R
    · obtain ⟨z, hyz, hz⟩ := exists_neighbor_not_mem_residual hSides hEven y
      have hsub : fiber y ⊆ univ \ S z := by
        intro p hp
        exact mem_sdiff.mpr ⟨mem_univ _, fun hs =>
          hSeparated y hy z hz hyz p hs (mem_filter.mp hp).2⟩
      have hc := card_sdiff_add_card_eq_card (subset_univ (S z))
      have hcube : (univ : Finset (Q 3)).card = 8 := by simp [Q, Sensitivity.Q]
      rw [hCard z hz, hcube] at hc
      exact (card_le_card hsub).trans (by omega)
    · exact (card_le_card (fun p hp => hOccupied y hy p (mem_filter.mp hp).2)).trans
        (hCard y hy).le
  calc
    U.card = ∑ y : Q 6, (U.filter fun e => e.2 = y).card :=
      card_eq_sum_card_fiberwise (f := Prod.snd) (by intro e he; simp)
    _ = ∑ y : Q 6, (fiber y).card := by
      apply sum_congr rfl
      intro y _
      have h : U.filter (fun e => e.2 = y) = (fiber y).image (fun p => (p, y)) := by
        ext ⟨p, z⟩
        by_cases hz : z = y
        · subst z
          simp [fiber]
        · simp [fiber, hz, Ne.symm hz]
      rw [h, card_image_of_injective _ (fun _ _ he => congrArg Prod.fst he)]
    _ ≤ ∑ _y : Q 6, 4 := sum_le_sum fun y _ => hBound y
    _ = 256 := by simp [Q, Sensitivity.Q]

#print axioms exists_neighbor_not_mem_residual
#print axioms card_le_256_of_residual_fibers

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q6EvenResidualNeighborhood
