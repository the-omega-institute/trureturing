/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Singular masks force pairs and triples of actual component directions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedGram
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! Masked Huang defects force local direction coverage in actual components. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DirectionCoverage

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions mem_directions directions_card)
open TwoBalancedComponents (componentFinset componentFinset_subset)
open SupportedEigenSaturation (selected_neighbor_card)
open Q9ComponentSaturation (componentDefect componentParityFinset
  exists_two_weighted_singular_components)
open Q9MaskedGram (maskWeight componentDefect_mask_det_ne_zero)

private abbrev Comp (U : Finset (Q 9)) :=
  ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent

open Classical in
private theorem exists_active_directions (U : Finset (Q 9)) (b : Bool) (C : Comp U)
    (I : Finset (Fin 9)) (d : ℕ) (hgap : d * d < I.card)
    (hsingular : (componentDefect (maskWeight I) U b C).det = 0) :
    ∃ x ∈ componentFinset U C, d < (I ∩ directions (componentFinset U C) x).card := by
  classical
  by_contra! h
  have bound (p q : Bool) (x : Q 9) (hx : x ∈ componentParityFinset U p C) :
      (I.filter fun a => flip x a ∈ componentParityFinset U q C).card ≤ d := by
    have hsub : (I.filter fun a => flip x a ∈ componentParityFinset U q C) ⊆
        I ∩ directions (componentFinset U C) x := by
      intro a ha
      obtain ⟨haI, haC⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_inter.mpr ⟨haI, (mem_directions _ _ _).mpr
        (Finset.mem_filter.mp haC).1⟩
    exact (Finset.card_le_card hsub).trans (h x (Finset.mem_filter.mp hx).1)
  exact componentDefect_mask_det_ne_zero U b C I (bound b (!b)) (bound (!b) b) hgap hsingular

open Classical in
/-- For each two-axis mask with singular defect, one actual component vertex
has both coordinate neighbors in the component. -/
theorem exists_pair_directions (U : Finset (Q 9)) (b : Bool) (C : Comp U)
    (I : Finset (Fin 9)) (hI : I.card = 2)
    (hsingular : (componentDefect (maskWeight I) U b C).det = 0) :
    ∃ x ∈ componentFinset U C, I ⊆ directions (componentFinset U C) x := by
  obtain ⟨x, hx, hcard⟩ := exists_active_directions U b C I 1 (by rw [hI]; decide) hsingular
  have heq : I ∩ directions (componentFinset U C) x = I :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  refine ⟨x, hx, ?_⟩
  rw [← heq]
  exact Finset.inter_subset_right

open Classical in
/-- For each five-axis mask with singular defect, one actual component vertex
has at least three coordinate neighbors in the mask. -/
theorem exists_three_directions_in_five_mask (U : Finset (Q 9)) (b : Bool) (C : Comp U)
    (I : Finset (Fin 9)) (hI : I.card = 5)
    (hsingular : (componentDefect (maskWeight I) U b C).det = 0) :
    ∃ x ∈ componentFinset U C, 3 ≤ (I ∩ directions (componentFinset U C) x).card := by
  exact exists_active_directions U b C I 2 (by rw [hI]; decide) hsingular

open Classical in
/-- If a component has at most three directions at each vertex, a singular
five-axis mask contains the whole three-axis direction set of some vertex. -/
theorem exists_direction_type_in_five_mask (U : Finset (Q 9)) (b : Bool) (C : Comp U)
    (hdeg : ∀ x ∈ componentFinset U C, (directions (componentFinset U C) x).card ≤ 3)
    (I : Finset (Fin 9)) (hI : I.card = 5)
    (hsingular : (componentDefect (maskWeight I) U b C).det = 0) :
    ∃ x ∈ componentFinset U C,
      (directions (componentFinset U C) x).card = 3 ∧ directions (componentFinset U C) x ⊆ I := by
  obtain ⟨x, hx, hthree⟩ := exists_three_directions_in_five_mask U b C I hI hsingular
  have hsub : I ∩ directions (componentFinset U C) x ⊆ directions (componentFinset U C) x :=
    Finset.inter_subset_right
  have hle := Finset.card_le_card hsub
  have hcap := hdeg x hx
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨x, hx, by omega, ?_⟩
  rw [← heq]
  exact Finset.inter_subset_left

open Classical in
private theorem component_directions_le_three (U : Finset (Q 9)) (C : Comp U)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (x : Q 9) (hx : x ∈ componentFinset U C) :
    (directions (componentFinset U C) x).card ≤ 3 := by
  classical
  have hsub := componentFinset_subset U C
  have hd : (directions (componentFinset U C) x).card ≤ (directions U x).card := by
    apply Finset.card_le_card
    intro a ha
    exact (mem_directions _ _ _).mpr (hsub ((mem_directions _ _ _).mp ha))
  have hf : U.filter (fun y => (hypercube 9).Adj x y) =
      (hypercube 9).neighborFinset x ∩ U := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  refine hd.trans ?_
  rw [directions_card, hf, selected_neighbor_card (hsub hx)]
  exact hdeg ⟨x, hsub hx⟩

open Classical in
/-- A subcubic 258-vertex support has two distinct actual components, each
realizing every direction pair and an entire three-axis type in every five-set. -/
theorem exists_two_direction_covering_components (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (b : Bool) :
    let covers := fun C : Comp U =>
      (∀ I : Finset (Fin 9), I.card = 2 →
        ∃ x ∈ componentFinset U C, I ⊆ directions (componentFinset U C) x) ∧
      (∀ I : Finset (Fin 9), I.card = 5 →
        ∃ x ∈ componentFinset U C,
          (directions (componentFinset U C) x).card = 3 ∧
          directions (componentFinset U C) x ⊆ I)
    ∃ C D : Comp U, C ≠ D ∧ covers C ∧ covers D := by
  classical
  obtain ⟨C, D, hCD, hsingular⟩ := exists_two_weighted_singular_components U hU hdeg b
  refine ⟨C, D, hCD, ?_, ?_⟩
  · exact ⟨fun I hI => exists_pair_directions U b C I hI (hsingular (maskWeight I)).1,
      fun I hI => exists_direction_type_in_five_mask U b C
        (component_directions_le_three U C hdeg) I hI (hsingular (maskWeight I)).1⟩
  · exact ⟨fun I hI => exists_pair_directions U b D I hI (hsingular (maskWeight I)).2,
      fun I hI => exists_direction_type_in_five_mask U b D
        (component_directions_le_three U D hdeg) I hI (hsingular (maskWeight I)).2⟩

#print axioms exists_pair_directions
#print axioms exists_three_directions_in_five_mask
#print axioms exists_direction_type_in_five_mask
#print axioms exists_two_direction_covering_components

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DirectionCoverage
