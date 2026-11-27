/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSharedFace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSharedFace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Both exterior midpoints see exactly the same two occupied corners. The two face swaps change the relative sign, which prevents cancellation at both midpoints. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CoherentExteriorFragment

/-! Shared midpoint cancellation rules out a monochromatic pair across a face
when both of its midpoints are adjacent to the opposite support. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSharedFace

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec cubeBitVec_xor_single)
open Q9SharedContactCNF (Word)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj flip_flip)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9IsotropicHuang (parity)
open Q9FiveAxisOrbitGeometry (MidpointCounts)
open Q9CoherentExteriorFragment (no_two_neighbor_pair_at_both_corners)

open Classical in
private theorem exterior_exactly_two {C D : Finset (Q 9)} {h : Q 9}
    {i j k : Fin 9} (hij : i ≠ j) (hi : flip h i ∈ C) (hj : flip h j ∈ C)
    (hk : flip h k ∈ D) (hp : parity (flip h i) = false)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) (counts : MidpointCounts C D) :
    h ∉ C ∧ directions C h = {i, j} := by
  have hOutside : h ∉ C := by
    intro hh
    have hd := hsep h hh _ hk
    rw [flip_adj] at hd
    omega
  have hsub : ({i, j} : Finset (Fin 9)) ⊆ directions C h := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (mem_directions C h _).mpr hi
    · obtain rfl := Finset.mem_singleton.mp ha
      exact (mem_directions C h _).mpr hj
  refine ⟨hOutside, (Finset.eq_of_subset_of_card_le hsub ?_).symm⟩
  rw [(counts h i k hi hk hp).1, Finset.card_pair hij]

open Classical in
/-- A face whose occupied diagonal is even cannot have both other vertices
adjacent to the opposite support. -/
theorem no_two_shared_midpoints_of_face {C D : Finset (Q 9)} {h : Q 9}
    {i j a b : Fin 9} (hij : i ≠ j)
    (hi : flip h i ∈ C) (hj : flip h j ∈ C)
    (ha : flip h a ∈ D) (hb : flip (flip (flip h i) j) b ∈ D)
    (hp : parity (flip h i) = false) (hq : parity (flip h j) = false)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) (counts : MidpointCounts C D)
    (hregular : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced C) : False := by
  have e₁ : flip (flip (flip h i) j) i = flip h j := by
    rw [flip_comm h i j, BalancedCriticalSpectrum.flip_flip]
  have e₂ : flip (flip (flip h i) j) j = flip h i := BalancedCriticalSpectrum.flip_flip _ _
  obtain ⟨hh, hfirst⟩ := exterior_exactly_two hij hi hj ha hp hsep counts
  have hi' : flip (flip (flip h i) j) i ∈ C := e₁.symm ▸ hj
  have hj' : flip (flip (flip h i) j) j ∈ C := e₂.symm ▸ hi
  have hq' : parity (flip (flip (flip h i) j) i) = false := e₁.symm ▸ hq
  obtain ⟨hu, hsecond⟩ := exterior_exactly_two hij hi' hj' hb hq' hsep counts
  exact no_two_neighbor_pair_at_both_corners hregular hbalanced hij hh hfirst hu hsecond

open Classical in
/-- The representative containing 0 and 6 on the first shore and 3 and 5
on the second has a face with both midpoints shared. -/
theorem no_rooted_shared_face {C D : Finset (Q 9)}
    (h0 : cubeBitVec 9 (0 : Word) ∈ C) (h6 : cubeBitVec 9 (6 : Word) ∈ C)
    (h3 : cubeBitVec 9 (3 : Word) ∈ D) (h5 : cubeBitVec 9 (5 : Word) ∈ D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) (counts : MidpointCounts C D)
    (hregular : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced C) : False := by
  have step (w : Word) (a : Fin 9) :
      flip (cubeBitVec 9 w) a = cubeBitVec 9 (w ^^^ BitVec.ofNat 9 (2 ^ a.val)) :=
    (cubeBitVec_xor_single w a).symm
  apply no_two_shared_midpoints_of_face (h := cubeBitVec 9 (2 : Word))
    (i := 1) (j := 2) (a := 0) (b := 0) (by decide)
    (hsep := hsep) (counts := counts) (hregular := hregular) (hbalanced := hbalanced)
  · rwa [step]
  · rwa [step]
  · rwa [step]
  · rwa [step, step, step]
  · rw [step]
    decide +kernel
  · rw [step]
    decide +kernel

open Classical in
/-- The whole second orbit is impossible. Its stabilizer preserves the
four occupied words that witness the shared face. -/
theorem no_second_orbit {C D : Finset (Q 9)} {p : Q9FiveAxisOrbitCover.Pattern}
    (hp : p ∈ Q9FiveAxisOrbitCover.orbit Q9FiveAxisOrbitCover.representatives[1]!)
    (hmatch : ∀ (s : Bool) (w : Word), w.toNat < 32 →
      parity (cubeBitVec 9 w) = false →
      (cubeBitVec 9 w ∈ Q9TightDistanceTwoCNF.support C D s ↔
        w ∈ Q9FiveAxisOrbitCover.Pattern.on p s))
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) (counts : MidpointCounts C D)
    (hregular : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced C) : False := by
  have hface : ∀ q ∈ Q9FiveAxisOrbitCover.orbit Q9FiveAxisOrbitCover.representatives[1]!,
      (0 : Word) ∈ q.1 ∧ (6 : Word) ∈ q.1 ∧ (3 : Word) ∈ q.2 ∧ (5 : Word) ∈ q.2 := by
    decide +kernel
  obtain ⟨h0, h6, h3, h5⟩ := hface p hp
  exact no_rooted_shared_face
    ((hmatch false 0 (by decide) (by decide +kernel)).mpr h0)
    ((hmatch false 6 (by decide) (by decide +kernel)).mpr h6)
    ((hmatch true 3 (by decide) (by decide +kernel)).mpr h3)
    ((hmatch true 5 (by decide) (by decide +kernel)).mpr h5)
    hsep counts hregular hbalanced

#print axioms no_second_orbit

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSharedFace
