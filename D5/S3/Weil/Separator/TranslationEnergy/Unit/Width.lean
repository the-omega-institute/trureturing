/- GID: D5/S3/Weil/Separator/TranslationEnergy/Unit/Width
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Unit/Width
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Bound the actual rounded unit payload and its canonical aggregate by the mesh mass. -/

import D5.S3.Weil.Separator.TranslationEnergy.UnitAcceptance
import D5.S3.Weil.Separator.TranslationEnergy.CutoffIntervals
import D5.S3.Weil.Separator.TranslationEnergy.SignedSquares
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy.Unit

open D5.S3.Weil.Separator.TranslationEnergy
open D5.S3.Weil.Separator.TranslationEnergy.CutoffIntervals
open D5.S3.Weil.Separator.TranslationEnergy.SignedSquares
open scoped BigOperators

/-- One actual unit payload contributes at most a quadratic mesh error and a
constant scalar/rounding error, with no sign assumption on its differences. -/
theorem unit_cell_width (R : Nat) (hR : 0 < R) (a b s : Rat) (hab : a ≤ b)
    (m : Nat) :
    (unitPolynomialPayload R a b s m (4 * m + 4)).norm.total.2 -
      (unitPolynomialPayload R a b s m (4 * m + 4)).norm.total.1 ≤
      72 * ((b - a) / R) + 16 * (1 / 2 : Rat) ^ m + 16 / (2 ^ 32 : Rat) := by
  have rounded_width (box : Rat × Rat) :
      (roundedInterval box).2 - (roundedInterval box).1 ≤
        box.2 - box.1 + 2 / (2 ^ 32 : Rat) := by
    have hp : (0 : Rat) < 2 ^ 32 := by positivity
    have hl := Int.lt_floor_add_one (box.1 * (2 ^ 32 : Rat))
    have hu := Int.ceil_lt_add_one (box.2 * (2 ^ 32 : Rat))
    dsimp [roundedInterval]
    have hla : box.1 - 1 / (2 ^ 32 : Rat) ≤
        ((Int.floor (box.1 * (2 ^ 32 : Rat)) : Int) : Rat) / (2 ^ 32 : Rat) := by
      apply (le_div_iff₀ hp).mpr
      have := le_of_lt hl
      field_simp at *
      linarith
    have hua : ((Int.ceil (box.2 * (2 ^ 32 : Rat)) : Int) : Rat) / (2 ^ 32 : Rat) ≤
        box.2 + 1 / (2 ^ 32 : Rat) := by
      apply (div_le_iff₀ hp).mpr
      have := le_of_lt hu
      field_simp at *
      linarith
    linarith

  have rounded_cutoff_range (box : Rat × Rat)
      (hlo : 0 ≤ box.1) (hhi : box.2 ≤ 1) (horder : box.1 ≤ box.2) :
      0 ≤ (roundedInterval box).1 ∧
      (roundedInterval box).1 ≤ (roundedInterval box).2 ∧
      (roundedInterval box).2 ≤ 1 := by
    have hp : (0 : Rat) < 2 ^ 32 := by positivity
    have hf : (0 : Rat) ≤ ((Int.floor (box.1 * (2 ^ 32 : Rat)) : Int) : Rat) := by
      have hi : (0 : Int) ≤ Int.floor (box.1 * (2 ^ 32 : Rat)) :=
        Int.le_floor.mpr (mul_nonneg hlo hp.le)
      exact_mod_cast hi
    have hc : ((Int.ceil (box.2 * (2 ^ 32 : Rat)) : Int) : Rat) ≤
        (2 ^ 32 : Rat) := by
      have hi : Int.ceil (box.2 * (2 ^ 32 : Rat)) ≤ (2 ^ 32 : Int) :=
        Int.ceil_le.mpr (by exact_mod_cast (mul_le_mul_of_nonneg_right hhi hp.le))
      exact_mod_cast hi
    have hflo := Int.floor_le (box.1 * (2 ^ 32 : Rat))
    have hceil := Int.le_ceil (box.2 * (2 ^ 32 : Rat))
    dsimp [roundedInterval]
    constructor
    · exact div_nonneg hf hp.le
    constructor
    · apply div_le_div_of_nonneg_right _ hp.le
      exact hflo.trans ((mul_le_mul_of_nonneg_right horder hp.le).trans hceil)
    · exact (div_le_iff₀ hp).mpr (by simpa using hc)
  have old_cutoff_width (a b : Rat) (hab : a ≤ b) :
      0 ≤ (cutoffCellBox R a b m (4 * m + 4)).1 ∧
      (cutoffCellBox R a b m (4 * m + 4)).1 ≤
        (cutoffCellBox R a b m (4 * m + 4)).2 ∧
      (cutoffCellBox R a b m (4 * m + 4)).2 ≤ 1 ∧
      (cutoffCellBox R a b m (4 * m + 4)).2 -
        (cutoffCellBox R a b m (4 * m + 4)).1 ≤
        9 * (b - a) / R + 2 * (1 / 2 : Rat) ^ m := by
    have old_abs_lower (a b : Rat) (hab : a ≤ b) :
        absLower a b = shiftedMinAbs a b 0 := by
      unfold absLower shiftedMinAbs
      by_cases ha : 0 ≤ a
      · have hb : 0 ≤ b := ha.trans hab
        simp only [add_zero, ha, if_pos]
        rw [abs_of_nonneg ha, abs_of_nonneg hb, min_eq_left hab]
        by_cases ha0 : a = 0
        · subst a; simp
        · rw [if_neg (by intro h; exact ha0 (le_antisymm h.1 ha))]
      · have ha' : a ≤ 0 := le_of_not_ge ha
        by_cases hb : b ≤ 0
        · by_cases hb0 : b = 0
          · subst b
            simp [ha, ha']
          · have hc : ¬ (a ≤ 0 ∧ 0 ≤ b) := by
              intro h
              exact hb0 (le_antisymm hb h.2)
            simp only [add_zero, hc, if_false, if_neg ha, if_pos hb]
            rw [abs_of_nonpos ha', abs_of_nonpos hb, min_eq_right (by linarith)]
        · have hb' : 0 ≤ b := le_of_not_ge hb
          simp [ha, hb, ha', hb']
    have hr : (0 : Rat) < R := by exact_mod_cast hR
    have h := shiftedCutoffInterval_certificate (R : Rat) a b 0 m hr hab
    have hid : cutoffCellBox R a b m (4 * m + 4) =
        shiftedCutoffInterval (R : Rat) a b 0 m := by
      simp [cutoffCellBox, shiftedCutoffInterval, cutoffInterval,
        cutoffArgLower, cutoffArgUpper, shiftedCutoffArgLower,
        shiftedCutoffArgUpper, old_abs_lower a b hab, absUpper, shiftedMaxAbs]
    rw [hid]
    rcases h with ⟨_, _, _, _, hlo, hord, hup, _, hw⟩
    refine ⟨hlo, hord, hup, ?_⟩
    convert hw using 1
    ring
  let u := cutoffCellBox R a b m (4 * m + 4)
  let v := cutoffCellBox R (a - s) (b - s) m (4 * m + 4)
  let x := roundedInterval u
  let y := roundedInterval v
  let l := x.1 - y.2
  let h := x.2 - y.1
  have hu := old_cutoff_width a b hab
  have hv := old_cutoff_width (a - s) (b - s) (by linarith)
  have huOrd : u.1 ≤ u.2 := hu.2.1
  have hvOrd : v.1 ≤ v.2 := hv.2.1
  have hx := rounded_cutoff_range u hu.1 hu.2.2.1 huOrd
  have hy := rounded_cutoff_range v hv.1 hv.2.2.1 hvOrd
  have hl : -(1 : Rat) ≤ l := by dsimp [l]; linarith [hx.1, hy.2.2]
  have hh : h ≤ (1 : Rat) := by dsimp [h]; linarith [hy.1, hx.2.2]
  have horder : l ≤ h := by dsimp [l, h]; linarith [hx.2.1, hy.2.1]
  have sq := square_bounds_width_le 1 l h (by norm_num) hl horder hh
  have heu := rounded_width u
  have hev := rounded_width v
  have hshift : b - s - (a - s) = b - a := by ring
  rw [hshift] at hv
  have hcut : (h - l) ≤
      18 * ((b - a) / R) + 4 * (1 / 2 : Rat) ^ m + 4 / (2 ^ 32 : Rat) := by
    dsimp only [l, h, x, y]
    linear_combination hu.2.2.2 + hv.2.2.2 + heu + hev
  change 2 * (squareBounds l h).2 - 2 * (squareBounds l h).1 ≤ _
  nlinarith [sq.2.2.2]

/-- The actual source-aligned aggregate contracts at the quadratic-mesh rate.
The statement quantifies over the canonical producer, not a user-supplied box. -/
theorem unit_aggregate_width (R : Nat) (hR : 0 < R) (s : Rat) (d m : Nat) :
    let L := supportHullUpper R s - supportHullLower R s
    let δ : Rat := 16 * (1 / 2 : Rat) ^ m + 16 / (2 ^ 32 : Rat)
    (aggregateBounds R s d (unitPolynomialPayloads R s d m (4 * m + 4))).2 -
        (aggregateBounds R s d (unitPolynomialPayloads R s d m (4 * m + 4))).1 ≤
      72 / (R : Rat) * ((L / ((2 ^ d : Nat) : Rat)) * L) + δ * L := by
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
  dsimp only
  let ps := unitPolynomialPayloads R s d m (4 * m + 4)
  let L := supportHullUpper R s - supportHullLower R s
  let δ : Rat := 16 * (1 / 2 : Rat) ^ m + 16 / (2 ^ 32 : Rat)
  have hacc := unitPolynomialPayloads_cells_accepted R hR s d m
  have hcount : ps.length + 1 = (canonicalPoints R s d).length := hacc.1
  have hlen : ps.length = (sourceCells R s d).length := by
    simp [ps, unitPolynomialPayloads]
  have hcell (i : Nat) (hi : i < ps.length) :
      ∃ a b, cellAt R s d i = some (a, b) ∧
        ps.getD i defaultPayload = unitPolynomialPayload R a b s m (4 * m + 4) := by
    have hj : i + 1 < (canonicalPoints R s d).length := by omega
    have hc := (show cellAt R s d i = some ((canonicalPoints R s d)[i],
        (canonicalPoints R s d)[i + 1]) from by
        simp [cellAt, List.getElem?_eq_getElem, hj,
          show i < (canonicalPoints R s d).length by omega])
    exact ⟨_, _, hc, hacc.2.2.2.1 i hi _ _ hc⟩
  have hsum : (aggregateBounds R s d ps).2 - (aggregateBounds R s d ps).1 =
      ∑ i ∈ Finset.range ps.length,
        canonicalCellLength R s d i *
          ((ps.getD i defaultPayload).norm.total.2 -
            (ps.getD i defaultPayload).norm.total.1) := by
    simp only [aggregateBounds, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨a, b, hc, _⟩ := hcell i (Finset.mem_range.mp hi)
    simp [hc, canonicalCellLength]
    ring
  have hr : (0 : Rat) < R := by exact_mod_cast hR
  have hbound : (∑ i ∈ Finset.range ps.length,
      canonicalCellLength R s d i *
        ((ps.getD i defaultPayload).norm.total.2 -
          (ps.getD i defaultPayload).norm.total.1)) ≤
      72 / (R : Rat) *
        (∑ i ∈ Finset.range ps.length, canonicalCellLength R s d i ^ 2) +
      δ * (∑ i ∈ Finset.range ps.length, canonicalCellLength R s d i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨a, b, hc, hp⟩ := hcell i (Finset.mem_range.mp hi)
    have hlenCell : canonicalCellLength R s d i = b - a := by simp [canonicalCellLength, hc]
    have hab : a ≤ b := (cellAt_strict R s d i a b hc).le
    have hw := unit_cell_width R hR a b s hab m
    rw [hp, hlenCell]
    have hmul := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hab)
    linear_combination hmul
  have hsq := sum_canonicalCellLength_sq_le R s d hR
  have hmass := sum_canonicalCellLength_eq_hull R s d
  have hcoeff : (0 : Rat) ≤ 72 / (R : Rat) := div_nonneg (by norm_num) hr.le
  rw [← hlen] at hsq hmass
  rw [hsum]
  calc
    _ ≤ 72 / (R : Rat) *
        (∑ i ∈ Finset.range ps.length, canonicalCellLength R s d i ^ 2) +
      δ * (∑ i ∈ Finset.range ps.length, canonicalCellLength R s d i) := hbound
    _ ≤ 72 / (R : Rat) * ((L / ((2 ^ d : Nat) : Rat)) * L) + δ * L := by
      rw [hmass]
      exact add_le_add (mul_le_mul_of_nonneg_left hsq hcoeff) le_rfl

#print axioms unit_cell_width
#print axioms unit_aggregate_width

end D5.S3.Weil.Separator.TranslationEnergy.Unit
