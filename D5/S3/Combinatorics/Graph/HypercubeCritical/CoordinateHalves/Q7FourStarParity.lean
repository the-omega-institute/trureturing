/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarParity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Root defect overlap and residual XOR cardinality for seven-cube stars. -/

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Root defect overlaps and residual parity defects for stars in Q7. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParity

private def directions : List (BitVec 7) := [1, 2, 4, 8, 16, 32, 64]

private def singleton (x : BitVec 7) : BitVec 128 := (1 : BitVec 128) <<< x.toNat

private def starMask (center axes : BitVec 7) : BitVec 128 :=
  directions.foldl (fun mask dir =>
    if axes &&& dir = 0 then mask else mask ||| singleton (center ^^^ dir)) (singleton center)

/-- The union of the translates of a star in its unused directions. Vertex and
axis labels are little-endian, and bit `x` of the result marks vertex `x`. -/
def starDefect (center axes : BitVec 7) : BitVec 128 :=
  directions.foldl (fun mask dir =>
    if axes &&& dir = 0 then mask ||| starMask (center ^^^ dir) axes else mask) 0

private def rootClosedNeighborhood : BitVec 128 :=
  directions.foldl (fun mask dir => mask ||| starMask dir 7) (starMask 0 7)

/-- A star is separated from the root star at center `0` with axes `7` if its
vertex mask misses the root's closed neighborhood. -/
def separatedFromRoot (center axes : BitVec 7) : Bool :=
  decide (starMask center axes &&& rootClosedNeighborhood = 0)

/-- The number of vertices common to the star's defect and the root defect. -/
def rootDefectOverlap (center axes : BitVec 7) : Nat :=
  (starDefect 0 7 &&& starDefect center axes).cpop.toNat

/-- The XOR of the defects of the root star, the second star at 24, and the third star. -/
def residual (secondAxes center axes : BitVec 7) : BitVec 128 :=
  starDefect 0 7 ^^^ starDefect 24 secondAxes ^^^ starDefect center axes

private def axisChoices : List (BitVec 7) :=
  [7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 35, 37, 38, 41, 42, 44, 49, 50, 52, 56,
    67, 69, 70, 73, 74, 76, 81, 82, 84, 88, 97, 98, 100, 104, 112]

private theorem mem_axisChoices {axes : BitVec 7} (h : axes.cpop = 3) :
    axes ∈ axisChoices := by
  have checked : (List.finRange 128).all (fun i =>
      decide ((BitVec.ofFin i : BitVec 7).cpop = 3 → BitVec.ofFin i ∈ axisChoices)) = true := by
    decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp checked axes.toFin
    (List.mem_finRange _))) h

private def parallelCenters : List (BitVec 7) := [40, 48, 72, 80, 96, 120]

-- Splitting the 128 centers into blocks keeps each kernel reduction small.
private def centerInBlock (block : Fin 16) (offset : Fin 8) : BitVec 7 :=
  BitVec.ofNat 7 (8 * block.val + offset.val)

private theorem exists_centerInBlock (center : BitVec 7) :
    ∃ (block : Fin 16) (offset : Fin 8), centerInBlock block offset = center := by
  have hlt : center.toNat < 128 := center.isLt
  let block : Fin 16 := ⟨center.toNat / 8, by omega⟩
  let offset : Fin 8 := ⟨center.toNat % 8, Nat.mod_lt _ (by decide)⟩
  refine ⟨block, offset, BitVec.eq_of_toNat_eq ?_⟩
  simp only [centerInBlock, block, offset, BitVec.toNat_ofNat]
  omega

private def checkOverlapBlock (block : Fin 16) : Bool :=
  (List.finRange 8).all fun offset =>
    let center := centerInBlock block offset
    axisChoices.all fun axes =>
      if separatedFromRoot center axes then
        let overlap := rootDefectOverlap center axes
        decide (overlap % 2 = 0 ∧
          (6 ≤ overlap → center.cpop = 2 ∧ center &&& 7 = 0 ∧
            (axes = 7 ∨ (axes &&& 7).cpop = 2 ∧ axes &&& center = 0)))
      else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem overlapBlocks_checked (block : Fin 16) : checkOverlapBlock block = true := by
  fin_cases block <;> decide +kernel

/-- A separated three-axis star has even defect overlap with the root. An overlap
of at least six forces two center coordinates outside the root axes. The axes
are either the root axes or two root axes and one axis outside the center and
the root axes.

For the parallel case, fix the root axes, send the two center coordinates to 3
and 4, and send the other two coordinates to 5 and 6. For the nonparallel case,
send the two selected root axes to 0 and 1, the remaining root axis to 2, the
center coordinates to 3 and 4, the selected outside axis to 5, and the remaining
coordinate to 6. Map each pair in increasing order. These permutations preserve
the root star and send the second star to center 24 with axes 7 or 35,
respectively. -/
theorem root_defect_overlap_classification {center axes : BitVec 7}
    (ha : axes.cpop = 3) (hsep : separatedFromRoot center axes = true) :
    (rootDefectOverlap center axes) % 2 = 0 ∧
      (6 ≤ rootDefectOverlap center axes → center.cpop = 2 ∧ center &&& 7 = 0 ∧
        (axes = 7 ∨ (axes &&& 7).cpop = 2 ∧ axes &&& center = 0)) := by
  obtain ⟨block, offset, rfl⟩ := exists_centerInBlock center
  have h := List.all_eq_true.mp (overlapBlocks_checked block) offset (List.mem_finRange _)
  have h := List.all_eq_true.mp h axes (mem_axisChoices ha)
  rw [ite_eq_left hsep] at h
  exact of_decide_eq_true h

private def checkBlock (block : Fin 16) : Bool :=
  (List.finRange 8).all fun offset =>
    let center := centerInBlock block offset
    if center = 0 ∨ center = 24 then true
    else axisChoices.all fun axes =>
      decide ((residual 7 center axes).cpop = 16 ↔ axes = 7 ∧ center ∈ parallelCenters) &&
      decide ((residual 35 center axes).cpop ≠ 16)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Each of the sixteen blocks checks up to 280 center and axis pairs.
private theorem blocks_checked (block : Fin 16) : checkBlock block = true := by
  fin_cases block <;> decide +kernel

private theorem residual_check {center axes : BitVec 7} (ha : axes.cpop = 3)
    (h0 : center ≠ 0) (h24 : center ≠ 24) :
    ((residual 7 center axes).cpop = 16 ↔ axes = 7 ∧ center ∈ parallelCenters) ∧
      (residual 35 center axes).cpop ≠ 16 := by
  obtain ⟨block, offset, rfl⟩ := exists_centerInBlock center
  have h := List.all_eq_true.mp (blocks_checked block) offset (List.mem_finRange _)
  rw [ite_eq_right (not_or.mpr ⟨h0, h24⟩)] at h
  have ha' := List.all_eq_true.mp h axes (mem_axisChoices ha)
  exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp ha').1,
    of_decide_eq_true (Bool.and_eq_true_iff.mp ha').2⟩

/-- For the parallel second star, the residual has size sixteen exactly at the
six listed centers with the original axes. Distinct centers suffice. -/
theorem parallel_residual_card_eq_sixteen_iff {center axes : BitVec 7}
    (ha : axes.cpop = 3) (h0 : center ≠ 0) (h24 : center ≠ 24) :
    (residual 7 center axes).cpop = 16 ↔
      axes = 7 ∧ center ∈ ([40, 48, 72, 80, 96, 120] : List (BitVec 7)) :=
  (residual_check ha h0 h24).1

/-- The second star with axes 0, 1, 5 admits no size-sixteen residual
from a three-axis star with a fresh center. -/
theorem nonparallel_residual_card_ne_sixteen {center axes : BitVec 7}
    (ha : axes.cpop = 3) (h0 : center ≠ 0) (h24 : center ≠ 24) :
    (residual 35 center axes).cpop ≠ 16 :=
  (residual_check ha h0 h24).2

#print axioms root_defect_overlap_classification
#print axioms parallel_residual_card_eq_sixteen_iff
#print axioms nonparallel_residual_card_ne_sixteen

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParity
