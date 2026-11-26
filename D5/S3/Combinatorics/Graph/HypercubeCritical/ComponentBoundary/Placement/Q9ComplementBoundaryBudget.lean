/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ComplementBoundaryBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A 258-vertex subcubic restriction of the nine-cube leaves room for at most 369 omitted edges. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorEdgeLiftCount

/-! A 258-vertex subcubic restriction leaves room for at most 369 omitted cube edges. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ComplementBoundaryBudget

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions directions_card mem_directions)
open SupportedEigenSaturation (selected_neighbor_card)
open private Dart darts tagged card_darts card_tagged mem_tagged from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorEdgeLiftCount

private theorem direction_count_union {A B : Finset (Q 9)} (hd : Disjoint A B) (x : Q 9) :
    (directions (A ∪ B) x).card = (directions A x).card + (directions B x).card := by
  classical
  have hu : directions (A ∪ B) x = directions A x ∪ directions B x := by
    ext i
    simp
  rw [hu, card_union_of_disjoint]
  exact disjoint_left.mpr fun i hi hj =>
    disjoint_left.mp hd ((mem_directions A x i).mp hi) ((mem_directions B x i).mp hj)

private theorem direction_sum_swap (A B : Finset (Q 9)) :
    ∑ x ∈ A, (directions B x).card = ∑ y ∈ B, (directions A y).card := by
  classical
  change ∑ x ∈ A, (directions B x).card = ∑ x ∈ B, (directions A x).card
  rw [← card_tagged, ← card_tagged]
  let reverse (d : Dart) : Dart := (flip d.1 d.2, d.2)
  have hrev (p : Dart) : reverse (reverse p) = p := by
    obtain ⟨x, i⟩ := p
    simp [reverse, BalancedCriticalSpectrum.flip_flip]
  have hmem {S T : Finset (Q 9)} {p : Dart} (hp : p ∈ darts S T) :
      reverse p ∈ darts T S := by
    obtain ⟨x, i⟩ := p
    obtain ⟨hx, hi⟩ := mem_tagged.mp hp
    exact mem_tagged.mpr ⟨(mem_directions T x i).mp hi,
      (mem_directions S (flip x i) i).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx)⟩
  have hinj : Function.Injective reverse := fun p q hp => by
    simpa only [hrev] using congrArg reverse hp
  apply le_antisymm
  · exact card_le_card_of_injOn reverse (fun _ hp => hmem hp) hinj.injOn
  · exact card_le_card_of_injOn reverse (fun _ hp => hmem hp) hinj.injOn

open Classical in
/-- The complement of a 258-vertex subcubic induced restriction has at most
738 oriented edges. -/
theorem complement_darts_le
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∑ x ∈ univ \ U, (directions (univ \ U) x).card ≤ 738 := by
  let V := univ \ U
  have hcardV : V.card = 254 := by
    simp only [V, card_univ_sdiff, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, hU]
    decide
  have hdis : Disjoint U V := disjoint_left.mpr fun _ hx hy => (mem_sdiff.mp hy).2 hx
  have hcover : U ∪ V = univ := by ext x; simp [V, Classical.em]
  have htot (x : Q 9) : (directions U x).card + (directions V x).card = 9 := by
    rw [← direction_count_union hdis, hcover]
    have hu : directions univ x = univ := by ext i; simp
    simp [hu]
  have hUbound (x : Q 9) (hx : x ∈ U) : (directions U x).card ≤ 3 := by
    rw [directions_card]
    have he : U.filter (fun y => (hypercube 9).Adj x y) = (hypercube 9).neighborFinset x ∩ U := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [he, selected_neighbor_card hx]
    exact hdeg ⟨x, hx⟩
  have hcross : 1548 ≤ ∑ x ∈ U, (directions V x).card := calc
    1548 = ∑ _x ∈ U, (6 : ℕ) := by simp [hU]
    _ ≤ _ := sum_le_sum fun x hx => by have := htot x; have := hUbound x hx; omega
  rw [direction_sum_swap] at hcross
  have hsum : (∑ x ∈ V, (directions U x).card) + ∑ x ∈ V, (directions V x).card = 2286 := by
    rw [← sum_add_distrib, sum_const_nat (fun x _ => htot x), hcardV]
  change ∑ x ∈ V, (directions V x).card ≤ 738
  omega

open Classical in
/-- Disjoint subsets of the complement spend its oriented-edge budget on
internal edges of either subset and on the edges crossing between them. -/
theorem packed_darts_le
    {A B V : Finset (Q 9)} (hA : A ⊆ V) (hB : B ⊆ V) (hAB : Disjoint A B) :
    2 * ((hypercube 9).induce (A : Set (Q 9))).edgeFinset.card +
      2 * ((hypercube 9).induce (B : Set (Q 9))).edgeFinset.card +
      2 * (∑ x ∈ A, (directions B x).card) ≤ ∑ x ∈ V, (directions V x).card := by
  have hcard (S : Finset (Q 9)) :
      2 * ((hypercube 9).induce (S : Set (Q 9))).edgeFinset.card =
        ∑ x ∈ S, (directions S x).card := by
    rw [← card_darts, card_tagged]
  rw [hcard A, hcard B]
  have hle : ∑ x ∈ A ∪ B, (directions (A ∪ B) x).card ≤ ∑ x ∈ V, (directions V x).card := by
    calc
      _ ≤ ∑ x ∈ A ∪ B, (directions V x).card := by
        apply sum_le_sum
        intro x _
        apply card_le_card
        intro i hi
        exact (mem_directions V x i).mpr (union_subset hA hB ((mem_directions (A ∪ B) x i).mp hi))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (union_subset hA hB) (by intros; omega)
  rw [sum_union hAB] at hle
  simp only [direction_count_union hAB, sum_add_distrib] at hle
  have hs := direction_sum_swap A B
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ComplementBoundaryBudget
