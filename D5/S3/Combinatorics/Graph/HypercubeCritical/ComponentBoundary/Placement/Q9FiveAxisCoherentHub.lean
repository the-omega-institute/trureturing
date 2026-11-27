/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisCoherentHub
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisCoherentHub
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The four corresponding contacts make the hub exterior. Its four coherent contributions require four further neighbors and exterior parity forces degree eight. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CoherentExteriorFragment
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedMidpointFiveAxes

/-! Signed cancellation bounds the number of leaves of a shared-midpoint star. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisCoherentHub

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedMidpointFiveAxes (two_neighbors_each)
open Q9CoherentExteriorFragment (twice_card_le_directions_of_coherent_exterior_fragment)

open Classical in
/-- If each face through a fixed leaf meets the opposite support at its outer
corner, the star has at most four leaves. With four leaves its hub is exterior
and has exactly eight neighbors in its own support. -/
theorem card_le_four_of_shared_faces
    {C D : Finset (Q 9)} {b : Bool} {h : Q 9} {i : Fin 9}
    {A I : Finset (Fin 9)} (hi : i ∈ A) (hA : A ⊆ directions C h)
    (hI : I.card ≤ 5) (hm : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ I)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hp : parity (flip h i) = b)
    (hshared : ∀ j ∈ A, i ≠ j → ∃ k : Fin 9, flip (flip (flip h i) j) k ∈ D) :
    A.card ≤ 4 ∧ (A.card = 4 → h ∉ C ∧ (directions C h).card = 8) := by
  have hfaces (j : Fin 9) (hj : j ∈ A) (hij : i ≠ j) :
      flip (flip h i) j ∉ C ∧ directions C (flip (flip h i) j) = {i, j} := by
    let v := flip (flip h i) j
    obtain ⟨k, hk⟩ := hshared j hj hij
    change flip v k ∈ D at hk
    have hvj : flip v j ∈ C := by
      simpa only [v, BalancedCriticalSpectrum.flip_flip] using (mem_directions C h i).mp (hA hi)
    have hvi : flip v i ∈ C := by
      change flip (flip (flip h i) j) i ∈ C
      rw [flip_comm h i j, BalancedCriticalSpectrum.flip_flip]
      exact (mem_directions C h j).mp (hA hj)
    have hvpar : parity (flip v j) = b := by simpa only [v, BalancedCriticalSpectrum.flip_flip] using hp
    have hcard := (two_neighbors_each hI hm hsep hrC hrD hbC hbD hvj hk hvpar).1
    have hsub : ({i, j} : Finset (Fin 9)) ⊆ directions C v := by
      intro a ha
      rcases mem_insert.mp ha with hi' | hj'
      · exact hi'.symm ▸ (mem_directions C v i).mpr hvi
      · have he := mem_singleton.mp hj'
        subst a
        exact (mem_directions C v j).mpr hvj
    change v ∉ C ∧ directions C v = {i, j}
    refine ⟨?_, (eq_of_subset_of_card_le hsub ?_).symm⟩
    · intro hv
      have he := hsep v hv _ hk
      have hd : hammingDist v (flip v k) = 1 := flip_adj v k
      omega
    · rw [hcard, card_pair hij]
  have hcap : (directions C h).card ≤ 9 :=
    (card_le_card (subset_univ _)).trans (by simp)
  by_cases hC : h ∈ C
  · have hs := card_le_card hA
    rw [regular_directions C hrC hC] at hs
    exact ⟨by omega, fun he => by omega⟩
  · have hs := twice_card_le_directions_of_coherent_exterior_fragment hrC hbC hC hi hA hfaces
    have heven := BalancedCubeComponentBoundary.exterior_even C hrC hbC h hC
    obtain ⟨m, hm⟩ := heven
    exact ⟨by omega, fun he => ⟨hC, by omega⟩⟩

#print axioms card_le_four_of_shared_faces

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisCoherentHub
