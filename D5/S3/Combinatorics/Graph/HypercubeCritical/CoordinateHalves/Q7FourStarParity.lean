/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarParity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Cardinality of the residual XOR for two fixed seven-cube star representatives. -/

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Residual parity defects for two fixed choices of the second star in Q7. -/

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
  have hlt : center.toNat < 128 := center.isLt
  let block : Fin 16 := ⟨center.toNat / 8, by omega⟩
  let offset : Fin 8 := ⟨center.toNat % 8, Nat.mod_lt _ (by decide)⟩
  have hc : centerInBlock block offset = center := by
    apply BitVec.eq_of_toNat_eq
    simp only [centerInBlock, block, offset, BitVec.toNat_ofNat]
    omega
  have h := List.all_eq_true.mp (blocks_checked block) offset (List.mem_finRange _)
  rw [hc, ite_eq_right (not_or.mpr ⟨h0, h24⟩)] at h
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

#print axioms parallel_residual_card_eq_sixteen_iff
#print axioms nonparallel_residual_card_ne_sixteen

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParity
