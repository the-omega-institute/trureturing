/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A balanced cubic Gray54 component limits a subcubic extension to 257 vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementReconstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixClosingCertificates
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Gray54ResidualCertificate

/-! Transport the normalized Gray residual bound to actual nine-cube candidates. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Gray54ExtensionBound

open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (IsBalanced)
open Q9GrayPlacementNormalForm (Vertex origin placement normalize normalize_placement
  normalize_hammingDist)
open Q9TriplePartitionOrbits (standardLabels)
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

attribute [local instance] Classical.propDecidable

private theorem card_le_of_normalized_residual_bound
    (hbound : let G := (placement standardLabels origin).map (cubeBitVec 9).symm.toEmbedding
      ∀ S : Finset (BitVec 9),
        (∀ v ∈ S, ∀ x ∈ G, 1 < hammingDist (cubeBitVec 9 v) (cubeBitVec 9 x)) →
        (∀ v ∈ S,
          (S.filter (fun x => hammingDist (cubeBitVec 9 v) (cubeBitVec 9 x) = 1)).card ≤ 3) →
        S.card ≤ 203)
    (U C : Finset Vertex) (hC : C.card = 54)
    (hr : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hsub : C ⊆ U)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hdeg : ∀ v : (U : Set Vertex), ((hypercube 9).induce (U : Set Vertex)).degree v ≤ 3) :
    U.card ≤ 257 := by
  obtain ⟨block, center, hblock, hplacement⟩ :=
    Q9GrayPlacementReconstruction.exists_placement_of_balanced_cubic C hC hr hb
  obtain ⟨σ, hσ⟩ := exists_perm_of_coordinate_color_counts standardLabels block (by
    intro b
    rw [hblock b]
    fin_cases b <;> decide +kernel)
  let e := normalize σ center
  let f := e.trans (cubeBitVec 9).symm
  let G := (placement standardLabels origin).map (cubeBitVec 9).symm.toEmbedding
  let W := U.map f.toEmbedding
  have horigin : e center = origin := by
    funext i
    change (center (σ i) != center (σ i)) = false
    simp
  have hG : C.map f.toEmbedding = G := by
    change C.map (e.toEmbedding.trans (cubeBitVec 9).symm.toEmbedding) = G
    rw [← map_map, hplacement,
      normalize_placement σ (Equiv.refl (Fin 3)) block standardLabels hσ center center]
    change (placement standardLabels (e center)).map (cubeBitVec 9).symm.toEmbedding = G
    rw [horigin]
  have hdist (x y : Vertex) : hammingDist (cubeBitVec 9 (f x)) (cubeBitVec 9 (f y)) =
      hammingDist x y := by
    simp only [f, e, Equiv.trans_apply, Equiv.apply_symm_apply, normalize_hammingDist]
  have hGW : G ⊆ W := by
    rw [← hG]
    exact map_subset_map.mpr hsub
  have hWdeg (v : BitVec 9) (hv : v ∈ W) :
      (W.filter (fun x => hammingDist (cubeBitVec 9 v) (cubeBitVec 9 x) = 1)).card ≤ 3 := by
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    have hfilter : U.filter (fun y => hammingDist x y = 1) =
        (hypercube 9).neighborFinset x ∩ U := by
      ext y
      simp only [mem_filter, mem_inter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    have hxdeg : (U.filter (fun y => hammingDist x y = 1)).card ≤ 3 := by
      rw [hfilter, selected_neighbor_card hx]
      exact hdeg ⟨x, hx⟩
    unfold W
    rw [filter_map, card_map]
    change (U.filter (fun y => hammingDist (cubeBitVec 9 (f x)) (cubeBitVec 9 (f y)) = 1)).card ≤ 3
    simpa only [hdist] using hxdeg
  have hres : (W \ G).card ≤ 203 := by
    apply hbound (W \ G)
    · intro v hv x hx
      obtain ⟨hvW, hvG⟩ := mem_sdiff.mp hv
      change x ∈ G at hx
      rw [← hG] at hx
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      obtain ⟨b, hbU, rfl⟩ := mem_map.mp hvW
      change 1 < hammingDist (cubeBitVec 9 (f b)) (cubeBitVec 9 (f a))
      rw [hdist b a, hammingDist_comm]
      have hne : a ≠ b := fun he => hvG (by rw [← he, ← hG]; exact mem_map.mpr ⟨a, ha, rfl⟩)
      have hzero : hammingDist a b ≠ 0 := fun he => hne (hammingDist_eq_zero.mp he)
      have hone : hammingDist a b ≠ 1 := fun he =>
        hvG (by rw [← hG]; exact mem_map.mpr ⟨b, hclosed a ha b hbU he, rfl⟩)
      omega
    · intro v hv
      exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans (hWdeg v (sdiff_subset hv))
  have hcard := card_sdiff_add_card_eq_card hGW
  have hGcard : G.card = 54 := by rw [← hG, card_map, hC]
  rw [hGcard, show W.card = U.card from card_map _] at hcard
  omega

#print axioms card_le_of_normalized_residual_bound

/-- A neighbor-closed, Huang-balanced cubic vertex set of order 54 limits a
subcubic extension in the nine-cube to at most 257 vertices. -/
theorem card_le_of_balanced_cubic_fifty_four
    (U C : Finset Vertex) (hC : C.card = 54)
    (hr : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hsub : C ⊆ U)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hdeg : ∀ v : (U : Set Vertex), ((hypercube 9).induce (U : Set Vertex)).degree v ≤ 3) :
    U.card ≤ 257 := by
  apply card_le_of_normalized_residual_bound _ U C hC hr hb hsub hclosed hdeg
  intro G S hsep hSdeg
  apply Q9Gray54ResidualCertificate.residual_card_le S _ hSdeg
  intro v hv
  apply (Q9Gray54ResidualCertificate.mem_residual_iff v).mpr
  rw [Q9Gray54ResidualCertificate.normalizedGray_eq_placement]
  exact hsep v hv

#print axioms card_le_of_balanced_cubic_fifty_four

/-- A 258-vertex subcubic candidate contains no neighbor-closed,
Huang-balanced cubic vertex set of order 54. -/
theorem card_ne_fifty_four_of_candidate
    (U C : Finset Vertex) (hU : U.card = 258)
    (hr : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hsub : C ⊆ U)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hdeg : ∀ v : (U : Set Vertex), ((hypercube 9).induce (U : Set Vertex)).degree v ≤ 3) :
    C.card ≠ 54 := by
  intro hC
  have hbound := card_le_of_balanced_cubic_fifty_four U C hC hr hb hsub hclosed hdeg
  omega

#print axioms card_ne_fifty_four_of_candidate

/-- A 258-vertex subcubic candidate contains two distinct actual
Huang-balanced cubic components, each with at least 72 vertices. -/
theorem exists_two_large_balanced_components (U : Finset Vertex) (hU : U.card = 258)
    (hdeg : ∀ v : (U : Set Vertex), ((hypercube 9).induce (U : Set Vertex)).degree v ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set Vertex)).ConnectedComponent,
      K ≠ L ∧ ∀ T ∈ ({K, L} : Set _),
        let C := TwoBalancedComponents.componentFinset U T
        ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3 ∧
          IsBalanced C ∧ 72 ≤ C.card := by
  obtain ⟨K, L, hKL, C, D, rfl, rfl, hC, hD, hCU, hDU, _, hclosedC, hclosedD,
    hrC, hrD, hbC, hbD, _⟩ := TwoBalancedComponents.exists_two_balanced_components U hU hdeg
  have large (S : Finset Vertex) (hS : S.Nonempty) (hSU : S ⊆ U)
      (hclosed : ∀ x ∈ S, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ S)
      (hr : ((hypercube 9).induce (S : Set Vertex)).IsRegularOfDegree 3)
      (hb : IsBalanced S) : 72 ≤ S.card :=
    (q9_balanced_induced_cubic_small_orders S hS hr hb).resolve_left
      (card_ne_fifty_four_of_candidate U S hU hr hb hSU hclosed hdeg)
  refine ⟨K, L, hKL, ?_⟩
  intro T hT
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
  rcases hT with rfl | rfl
  · exact ⟨hrC, hbC, large _ hC hCU hclosedC hrC hbC⟩
  · exact ⟨hrD, hbD, large _ hD hDU hclosedD hrD hbD⟩

#print axioms exists_two_large_balanced_components

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Gray54ExtensionBound
