/- GID: D5/S3/Weil/Separator/TranslationEnergy/Geometry
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Geometry
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: none
   digest: Telescope canonical cell lengths and bound their quadratic mass. -/

import D5.S3.Weil.Separator.TranslationEnergy.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy

open scoped BigOperators

def canonicalCellLength (R : Nat) (s : Rat) (d i : Nat) : Rat :=
  match cellAt R s d i with
  | none => 0
  | some (a, b) => b - a

theorem sum_canonicalCellLength_eq_hull (R : Nat) (s : Rat) (d : Nat) :
    (∑ i ∈ Finset.range (sourceCells R s d).length, canonicalCellLength R s d i) =
      supportHullUpper R s - supportHullLower R s := by
  let points := canonicalPoints R s d
  let n := (sourceCells R s d).length
  let x : Nat → Rat := fun i => points.getD i 0
  have hn : n + 1 = points.length := by
    simpa only [n, points] using sourceCells_length_add_one R s d
  have hfirst : x 0 = supportHullLower R s := by
    have h := canonicalPoints_first R s d
    simpa only [x, points, List.getD_eq_getElem?_getD, h, Option.getD_some]
  have hlast : x n = supportHullUpper R s := by
    have hn' : n = points.length - 1 := by omega
    have h := canonicalPoints_last R s d
    rw [← hn'] at h
    simpa only [x, points, List.getD_eq_getElem?_getD, h, Option.getD_some]
  calc
    (∑ i ∈ Finset.range (sourceCells R s d).length, canonicalCellLength R s d i) =
        ∑ i ∈ Finset.range n, (x (i + 1) - x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < n := by simpa only [Finset.mem_range, n] using hi
          have hiCell : i + 1 < (canonicalPoints R s d).length := by
            change i + 1 < points.length
            omega
          have heq : canonicalCellLength R s d i =
              (canonicalPoints R s d).getD (i + 1) 0 -
                (canonicalPoints R s d).getD i 0 := by
            rw [canonicalCellLength, (show cellAt R s d i = some ((canonicalPoints R s d)[i],
                  (canonicalPoints R s d)[i + 1]) from by
                  simp [cellAt, List.getElem?_eq_getElem, hiCell,
                    show i < (canonicalPoints R s d).length by omega])]
            simp only
            congr 1 <;> rw [List.getD_eq_getElem]
          exact heq
    _ = x n - x 0 := Finset.sum_range_sub x n
    _ = supportHullUpper R s - supportHullLower R s := by rw [hfirst, hlast]

theorem canonicalCellLength_nonneg (R : Nat) (s : Rat) (d i : Nat) :
    0 ≤ canonicalCellLength R s d i := by
  have cellAt_strict (R : Nat) (s : Rat) (d i : Nat) (a b : Rat)
      (hcell : cellAt R s d i = some (a, b)) : a < b := by
    have hi : i < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      simp [cellAt, hnone] at hcell
    have hj : i + 1 < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      rw [cellAt, List.getElem?_eq_getElem hi, hnone] at hcell
      simp at hcell
    rw [cellAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hcell
    change some ((canonicalPoints R s d)[i], (canonicalPoints R s d)[i + 1]) =
      some (a, b) at hcell
    injection hcell with hpair
    injection hpair with ha hb
    subst a
    subst b
    exact (Finset.sortedLT_sort (canonicalPointSet R s d)).getElem_lt_getElem_of_lt (by omega)
  rw [canonicalCellLength]
  split
  · exact le_rfl
  · next a b hcell => exact sub_nonneg.mpr (cellAt_strict R s d i a b hcell).le

theorem canonicalCellLength_le_mesh (R : Nat) (s : Rat) (d i : Nat) (hR : 0 < R) :
    canonicalCellLength R s d i ≤
      (supportHullUpper R s - supportHullLower R s) / ((2 ^ d : Nat) : Rat) := by
  rw [canonicalCellLength]
  split
  · have hr : (0 : Rat) ≤ R := by positivity
    have hhull : supportHullLower R s ≤ supportHullUpper R s :=
      (min_le_left _ _).trans ((show -(2 * (R : Rat)) ≤ 2 * R by
        linarith).trans (le_max_left _ _))
    exact div_nonneg (sub_nonneg.mpr hhull) (by positivity)
  · next a b hcell => exact cellAt_gap_le_mesh R s d i a b hR hcell

theorem sum_canonicalCellLength_sq_le (R : Nat) (s : Rat) (d : Nat) (hR : 0 < R) :
    (∑ i ∈ Finset.range (sourceCells R s d).length,
        (canonicalCellLength R s d i) ^ 2) ≤
      ((supportHullUpper R s - supportHullLower R s) / ((2 ^ d : Nat) : Rat)) *
        (supportHullUpper R s - supportHullLower R s) := by
  let gap : Rat :=
    (supportHullUpper R s - supportHullLower R s) / ((2 ^ d : Nat) : Rat)
  calc
    (∑ i ∈ Finset.range (sourceCells R s d).length,
        (canonicalCellLength R s d i) ^ 2) ≤
        ∑ i ∈ Finset.range (sourceCells R s d).length,
          gap * canonicalCellLength R s d i := by
            apply Finset.sum_le_sum
            intro i hi
            have hnonneg := canonicalCellLength_nonneg R s d i
            have hle : canonicalCellLength R s d i ≤ gap := by
              exact canonicalCellLength_le_mesh R s d i hR
            nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hle)]
    _ = gap *
        (∑ i ∈ Finset.range (sourceCells R s d).length,
          canonicalCellLength R s d i) := by rw [Finset.mul_sum]
    _ = gap * (supportHullUpper R s - supportHullLower R s) := by
      rw [sum_canonicalCellLength_eq_hull]

end D5.S3.Weil.Separator.TranslationEnergy
