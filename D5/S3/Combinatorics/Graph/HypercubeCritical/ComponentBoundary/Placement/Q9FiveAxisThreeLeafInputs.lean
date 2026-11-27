/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisThreeLeafInputs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisThreeLeafInputs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: At an exterior hub the three aligned contributions require three compensators. Hence any four directions contain at least one occupied neighbor. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFourLeafSigns

/-! The three-leaf occupancy clauses for the normalized five-axis branch. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisThreeLeafInputs

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves (toggle)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj flip_flip)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9FiveAxisFourLeafSigns (starMask)
open Q9SharedMidpointFiveAxes (two_neighbors_each)
open Q9CoherentExteriorFragment (twice_card_le_directions_of_coherent_exterior_fragment)
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private step_cube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFourLeafSigns

/-- The three partner axes in the little-endian input generator. -/
def partners : Finset (Fin 9) := {0, 3, 4}

private theorem starMask_eq_toggle :
    ∀ low : Fin 9, low = 1 ∨ low = 2 → starMask low = toggle (25 : BitVec 9) low := by
  decide +kernel

/-- On each face through axis 0, flipping the low axis at the far corner
reaches the shifted leaf of the remaining partner axis. -/
private theorem shared_face_mask :
    ∀ low : Fin 9, low = 1 ∨ low = 2 →
    ∀ j ∈ partners, (0 : Fin 9) ≠ j →
      ∃ l ∈ partners, toggle (toggle (toggle 0 0) j) low = toggle 0 l ^^^ starMask low := by
  decide +kernel

open Classical in
/-- The six leaves in `coherent_exterior_triples` force an exterior hub to
have at least six occupied directions. Every set of four axes contains an
occupied direction, including every four outward axes. -/
theorem coherent_exterior_triples
    {C D : Finset (Q 9)} {w : BitVec 9} {low : Fin 9} {I : Finset (Fin 9)}
    (hlow : low = 1 ∨ low = 2)
    (hI : I.card ≤ 5) (hm : ∀ T ∈ minimumDisplacements C D false 2, T ⊆ I)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hp : parity (cubeBitVec 9 w) = true)
    (hleft : ∀ i ∈ partners, cubeBitVec 9 (toggle w i) ∈ C)
    (hright : ∀ i ∈ partners, cubeBitVec 9 (toggle w i ^^^ toggle (25 : BitVec 9) low) ∈ D) :
    cubeBitVec 9 w ∈ C ∨
      ∀ S : Finset (Fin 9), S.card = 4 → ∃ a ∈ S, cubeBitVec 9 (toggle w a) ∈ C := by
  let h := cubeBitVec 9 w
  by_cases hh : h ∈ C
  · exact Or.inl hh
  have hzero : (0 : Fin 9) ∈ partners := by simp [partners]
  have hleaf (a : Fin 9) (ha : a ∈ partners) : flip h a ∈ C := by
    simpa only [step_cube] using hleft a ha
  have hsub : partners ⊆ directions C h :=
    fun a ha => (mem_directions C h a).mpr (hleaf a ha)
  have hpar : parity (flip h 0) = false := by
    rw [parity_flip]
    simp [h, hp]
  have hfaces (j : Fin 9) (hj : j ∈ partners) (hj0 : (0 : Fin 9) ≠ j) :
      flip (flip h 0) j ∉ C ∧ directions C (flip (flip h 0) j) = {0, j} := by
    let v := flip (flip h 0) j
    obtain ⟨l, hl, hm0⟩ := shared_face_mask low hlow j hj hj0
    have hw : toggle (toggle (toggle w 0) j) low = toggle w l ^^^ starMask low := by
      simp [toggle, BitVec.xor_assoc] at hm0 ⊢
      exact hm0
    have hv := congrArg (cubeBitVec 9) hw
    simp only [step_cube, starMask_eq_toggle low hlow] at hv
    have hvD : flip v low ∈ D := hv.symm ▸ hright l hl
    have hvj : flip v j ∈ C := by
      simpa only [v, BalancedCriticalSpectrum.flip_flip] using hleaf 0 hzero
    have hv0 : flip v 0 ∈ C := by
      change flip (flip (flip h 0) j) 0 ∈ C
      rw [flip_comm h 0 j, BalancedCriticalSpectrum.flip_flip]
      exact hleaf j hj
    have hvpar : parity (flip v j) = false := by
      simpa only [v, BalancedCriticalSpectrum.flip_flip] using hpar
    have hcard := (two_neighbors_each hI hm hsep hrC hrD hbC hbD hvj hvD hvpar).1
    have hpair : ({0, j} : Finset (Fin 9)) ⊆ directions C v := by
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact (mem_directions C v 0).mpr hv0
      · have he : a = j := mem_singleton.mp ha
        exact (he.symm ▸ (mem_directions C v j).mpr hvj)
    change v ∉ C ∧ directions C v = {0, j}
    refine ⟨?_, (eq_of_subset_of_card_le hpair ?_).symm⟩
    · intro hvC
      have hd := hsep v hvC _ hvD
      rw [flip_adj] at hd
      omega
    · rw [hcard, card_pair hj0]
  have hpartners : partners.card = 3 := by decide +kernel
  have hdegree : 6 ≤ (directions C h).card := by
    simpa only [hpartners] using
      twice_card_le_directions_of_coherent_exterior_fragment hrC hbC hh hzero hsub hfaces
  refine Or.inr ?_
  intro S hS
  by_contra hempty
  have hcap : directions C h ⊆ (univ : Finset (Fin 9)) \ S := by
    intro a ha
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro haS
    apply hempty
    refine ⟨a, haS, ?_⟩
    simpa only [step_cube] using (mem_directions C h a).mp ha
  have hle := card_le_card hcap
  rw [card_univ_sdiff, Fintype.card_fin, hS] at hle
  omega

#print axioms coherent_exterior_triples

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisThreeLeafInputs
