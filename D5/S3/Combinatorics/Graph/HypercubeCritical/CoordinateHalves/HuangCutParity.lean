/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangCutParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangCutParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Recover opposite-slice occupancy from the parity of a closed in-plane neighborhood. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Mathlib.Data.ZMod.Basic

/-! Modulo two, a Huang eigenvector records its support. The opposite
coordinate half can therefore be recovered using just vertex membership. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open BalancedCubeComponentBoundary (directions exterior_even regular_directions)
local notation "flip" => BalancedCriticalSpectrum.flip

attribute [local instance] Classical.propDecidable

private noncomputable def indicator (S : Finset (Q 9)) (x : Q 9) : ZMod 2 :=
  if x ∈ S then 1 else 0

/-- Count the occupied point and occupied neighbors other than the cut
neighbor, in the field of two elements. -/
noncomputable def halfParity (S : Finset (Q 9)) (x : Q 9) : ZMod 2 :=
  indicator S x + ∑ i ∈ Finset.univ.erase (0 : Fin 9), indicator S (flip x i)

/-- The occupancy of a point across the cut is the parity of the closed
neighborhood of its mirror point within the given half. -/
theorem mem_flip_iff_halfParity {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {b : Bool} {x : Q 9} (hx : x 0 = b) :
    flip x 0 ∈ C ↔ halfParity (coordinateSlice C b) x = 1 := by
  have hadd (a c : ZMod 2) : a - c = a + c := by
    revert a c
    decide
  have hf (u : Q 9) (hu : u 0 = b) : indicator C u = indicator (coordinateSlice C b) u := by
    simp [indicator, coordinateSlice, hu]
  have hcard : (∑ i : Fin 9, indicator C (flip x i)) = ((directions C x).card : ZMod 2) := by
    rw [directions, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : flip x i ∈ C <;> simp [indicator, h]
  have hrow : (∑ i : Fin 9, indicator C (flip x i)) = indicator C x := by
    rw [hcard]
    by_cases h : x ∈ C
    · rw [regular_directions C hr h, indicator, if_pos h]
      decide
    · obtain ⟨k, hk⟩ := exterior_even C hr hb x h
      rw [hk, ← two_mul, Nat.cast_mul, indicator, if_neg h]
      rw [show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin 9))] at hrow
  have hc : indicator C (flip x 0) = halfParity (coordinateSlice C b) x := by
    have hd := congrArg (fun t : ZMod 2 => t - ∑ i ∈ Finset.univ.erase (0 : Fin 9),
      indicator C (flip x i)) hrow
    rw [add_sub_cancel_left, hadd, hf x hx] at hd
    rw [halfParity, hd]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hf _ ((Function.update_of_ne (Finset.mem_erase.mp hi).1.symm _ _).trans hx)
  rw [← hc]
  simp [indicator]

#print axioms mem_flip_iff_halfParity

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
