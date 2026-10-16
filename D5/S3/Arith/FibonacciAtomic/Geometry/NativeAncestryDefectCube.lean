/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Equal-length context substitutions preserve a common coordinate exterior while the three-leaf defect swaps its two internal areas. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube

open GenealogicalFiberTransport (Source)
open ActualLeafHistoryRigidity (OutputContext)
open AncestorAreaInterval (coordinates offset)

/- The two three-leaf trees in the defect. -/
def defectB : Source := .mul (.mul (.of false) (.of true)) (.of false)
def defectD : Source := .mul (.of false) (.mul (.of true) (.of false))

private theorem coordinate_list_length (t : Source) : (coordinates t).length = t.length - 1 := by
  induction t with
  | of b => rfl
  | mul l r hl hr =>
      have hlp := FreeMagma.length_pos l
      have hrp := FreeMagma.length_pos r
      simp only [coordinates, List.length_append, List.length_singleton, hl, hr,
        FreeMagma.length]
      omega

private theorem plug_length (C : OutputContext) (x : Source) :
    (C.plug x).length = C.outsideLeaves + x.length := by
  induction C with
  | hole => simp [OutputContext.plug, OutputContext.outsideLeaves]
  | left C r ih =>
      simp only [OutputContext.plug, OutputContext.outsideLeaves, FreeMagma.length]
      omega
  | right l C ih =>
      simp only [OutputContext.plug, OutputContext.outsideLeaves, FreeMagma.length]
      omega

private theorem equal_length_coordinate_splice
    (C : OutputContext) (x y : Source) (hxy : x.length = y.length) :
    ∃ L R : List ℕ,
      coordinates (C.plug x) = L ++ coordinates x ++ R ∧
      coordinates (C.plug y) = L ++ coordinates y ++ R ∧
      L.length = offset (C.plug x) C.holeAddress := by
  induction C generalizing x y with
  | hole =>
      exact ⟨[], [], by simp [OutputContext.plug], by simp [OutputContext.plug],
        by simp [OutputContext.holeAddress, offset]⟩
  | left C r ih =>
      obtain ⟨L, R, hx, hy, hL⟩ := ih x y hxy
      have hlen : (C.plug x).length = (C.plug y).length := by
        rw [plug_length, plug_length, hxy]
      let Q : List ℕ := R ++ [(C.plug x).length * r.length] ++ coordinates r
      refine ⟨L, Q, ?_, ?_, ?_⟩
      · simp only [OutputContext.plug, coordinates, Q, hx, List.append_assoc]
      · simp only [OutputContext.plug, coordinates, Q, hy, hlen, List.append_assoc]
      · simpa only [OutputContext.holeAddress, OutputContext.plug, offset] using hL
  | right l C ih =>
      obtain ⟨L, R, hx, hy, hL⟩ := ih x y hxy
      have hlen : (C.plug x).length = (C.plug y).length := by
        rw [plug_length, plug_length, hxy]
      let P : List ℕ := coordinates l ++ [l.length * (C.plug x).length] ++ L
      refine ⟨P, R, ?_, ?_, ?_⟩
      · simp only [OutputContext.plug, coordinates, P, hx, List.append_assoc]
      · simp only [OutputContext.plug, coordinates, P, hy, hlen, List.append_assoc]
      · have hcoord : (coordinates l).length = l.length - 1 := coordinate_list_length l
        have hlpos := l.length_pos
        simp only [OutputContext.holeAddress, OutputContext.plug, offset, P,
          List.length_append, List.length_singleton, hcoord] at hL ⊢
        omega

private theorem defect_coordinates :
    coordinates defectB = [1, 2] ∧ coordinates defectD = [2, 1] := by
  decide

private theorem defect_length : defectB.length = defectD.length := by decide

def listSquaredDistance (x y : List ℕ) : ℤ :=
  (x.zipWith (fun a b => ((a : ℤ) - (b : ℤ))^2) y).sum

noncomputable def normalizedListDistance (m : ℕ) (x y : List ℕ) : ℝ :=
  Real.sqrt (listSquaredDistance x y) / (m.choose 2 : ℝ)

private theorem list_squared_distance_splice (L R : List ℕ) :
    listSquaredDistance (L ++ [1, 2] ++ R) (L ++ [2, 1] ++ R) = 2 := by
  induction L with
  | nil =>
      induction R with
      | nil => norm_num [listSquaredDistance]
      | cons r R ih => simpa [listSquaredDistance, List.append_assoc] using ih
  | cons l L ih =>
      simpa [listSquaredDistance, List.append_assoc] using ih

-- The context recursion and the exact list-distance calculation share a larger proof budget.
set_option maxHeartbeats 800000 in
/-- Every equal-length context transports the two internal defect coordinates
without changing the exterior coordinates or the occupied leaf offset. -/
theorem native_area_cube (C : OutputContext) :
    ∃ L R : List ℕ,
      coordinates (C.plug defectB) = L ++ [1, 2] ++ R ∧
      coordinates (C.plug defectD) = L ++ [2, 1] ++ R ∧
      L.length = offset (C.plug defectB) C.holeAddress ∧
      listSquaredDistance (L ++ [1, 2] ++ R) (L ++ [2, 1] ++ R) = 2 := by
  obtain ⟨L, R, hx, hy, hL⟩ :=
    equal_length_coordinate_splice C defectB defectD defect_length
  obtain ⟨hB, hD⟩ := defect_coordinates
  refine ⟨L, R, ?_, ?_, hL, ?_⟩
  · simpa [hB] using hx
  · simpa [hD] using hy
  · exact list_squared_distance_splice L R

-- The normalized edge reuses the contextual splice and its exact integer square sum.
set_option maxHeartbeats 800000 in
/-- The same contextual edge after division by the total pair count. -/
theorem normalized_cube_diameter (C : OutputContext) :
    ∃ L R : List ℕ,
      coordinates (C.plug defectB) = L ++ [1, 2] ++ R ∧
      coordinates (C.plug defectD) = L ++ [2, 1] ++ R ∧
      normalizedListDistance (C.plug defectB).length
        (L ++ [1, 2] ++ R) (L ++ [2, 1] ++ R) =
        Real.sqrt 2 / ((C.plug defectB).length.choose 2 : ℝ) := by
  obtain ⟨L, R, hx, hy, _, hsq⟩ := native_area_cube C
  refine ⟨L, R, hx, hy, ?_⟩
  simp only [normalizedListDistance, hsq, Int.cast_ofNat]

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.native_area_cube
