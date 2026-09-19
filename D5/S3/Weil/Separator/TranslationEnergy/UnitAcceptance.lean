/- GID: D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/UnitAcceptance
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Verify the rounded unit-polynomial producer on every canonical source cell. -/

import D5.S3.Weil.Separator.TranslationEnergy.Integral
import D5.S3.Weil.Separator.TranslationEnergy.Scalar.Uniform

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy

open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic
open D5.S3.Weil.Separator.TranslationEnergy.Scalar.Uniform

theorem check_unitPolynomialPayload (R : Nat) (hR : 0 < R) (s : Rat)
    (d i m : Nat) (a b : Rat) (hcell : cellAt R s d i = some (a, b)) :
    checkCanonicalCell R [1] [1] s d i m (4 * m + 4)
      (unitPolynomialPayload R a b s m (4 * m + 4)) = true := by
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
  have hab := (cellAt_strict R s d i a b hcell).le
  have hc (t : Rat) := (checkCutoffLogistic_all_precision t m).1
  have ordered (u v : Rat) :
      (cutoffCellBox R u v m (4 * m + 4)).1 ≤
        (cutoffCellBox R u v m (4 * m + 4)).2 := by
    have harg : cutoffArgLower R u v ≤ cutoffArgUpper R u v := by
      have hAbs : absLower u v ≤ absUpper u v := by
        unfold absLower absUpper
        split_ifs with hu hv
        · exact (le_abs_self u).trans (le_max_left _ _)
        · exact (neg_le_abs v).trans (le_max_right _ _)
        · exact (abs_nonneg u).trans (le_max_left _ _)
      unfold cutoffArgLower cutoffArgUpper
      exact sub_le_sub_left (div_le_div_of_nonneg_right hAbs (by positivity)) 2
    have hl := checked_cutoff_logistic_sound (cutoffArgLower R u v) m
      (4 * m + 4) (hc _)
    have hh := checked_cutoff_logistic_sound (cutoffArgUpper R u v) m
      (4 * m + 4) (hc _)
    have hr : ((cutoffCellBox R u v m (4 * m + 4)).1 : Real) ≤
        ((cutoffCellBox R u v m (4 * m + 4)).2 : Real) :=
      hl.2.1.trans ((Real.smoothTransition.monotone (by exact_mod_cast harg)).trans hh.2.2.1)
    exact_mod_cast hr
  have round (box : Rat × Rat) (hbox : box.1 ≤ box.2) :
      (roundedInterval box).1 ≤ box.1 ∧ box.2 ≤ (roundedInterval box).2 ∧
        (roundedInterval box).1 ≤ (roundedInterval box).2 := by
    have hp : (0 : Rat) < 2 ^ 32 := by positivity
    have hl : (roundedInterval box).1 ≤ box.1 := by
      exact (div_le_iff₀ hp).mpr (Int.floor_le (box.1 * (2 ^ 32 : Rat)))
    have hu : box.2 ≤ (roundedInterval box).2 := by
      exact (le_div_iff₀ hp).mpr (Int.le_ceil (box.2 * (2 ^ 32 : Rat)))
    exact ⟨hl, hu, hl.trans (hbox.trans hu)⟩
  let here := roundedInterval (cutoffCellBox R a b m (4 * m + 4))
  let shifted := roundedInterval (cutoffCellBox R (a - s) (b - s) m (4 * m + 4))
  let diff : Rat × Rat := (here.1 - shifted.2, here.2 - shifted.1)
  let sq := SignedSquares.squareBounds diff.1 diff.2
  have hh := round _ (ordered a b)
  have hs := round _ (ordered (a - s) (b - s))
  have hd : diff.1 ≤ diff.2 := by dsimp [diff]; linarith [hh.2.2, hs.2.2]
  have hsq : sq.1 ≤ sq.2 ∧
      (sq.1 ≤ 0 ∨ (0 ≤ diff.1 ∧ sq.1 ≤ diff.1 ^ 2) ∨
        (diff.2 ≤ 0 ∧ sq.1 ≤ diff.2 ^ 2)) ∧
      diff.1 ^ 2 ≤ sq.2 ∧ diff.2 ^ 2 ≤ sq.2 := by
    have hl := le_max_left (diff.1 ^ 2) (diff.2 ^ 2)
    have hu := le_max_right (diff.1 ^ 2) (diff.2 ^ 2)
    dsimp [sq, SignedSquares.squareBounds]
    split_ifs with hp hn
    · exact ⟨hl, Or.inr (Or.inl ⟨hp, le_rfl⟩), hl, hu⟩
    · exact ⟨hu, Or.inr (Or.inr ⟨hn, le_rfl⟩), hl, hu⟩
    · exact ⟨(sq_nonneg diff.1).trans hl, Or.inl le_rfl, hl, hu⟩
  have hnorm : check
      (cellInputBox R a b s m (4 * m + 4) (unitPolynomialPayload R a b s m (4 * m + 4)))
      (cellNormSqExpr R a b s m (4 * m + 4)
        (unitPolynomialPayload R a b s m (4 * m + 4))) = true := by
    simp only [cellNormSqExpr, unitPolynomialPayload]
    change check _ (.add (2 * sq.1) (2 * sq.2)
      (.square sq.1 sq.2 (.add diff.1 diff.2
        (.mul here.1 here.2 (.input 0 _ _) (.input 2 1 1))
        (.neg (-shifted.2) (-shifted.1)
          (.mul shifted.1 shifted.2 (.input 1 _ _) (.input 4 1 1)))))
      (.square sq.1 sq.2 (.add diff.1 diff.2
        (.mul here.1 here.2 (.input 0 _ _) (.input 3 1 1))
        (.neg (-shifted.2) (-shifted.1)
          (.mul shifted.1 shifted.2 (.input 1 _ _) (.input 5 1 1)))))) = true
    have ho := ordered a b
    have hso := ordered (a - s) (b - s)
    have hhc := hh.1.trans ho
    have hhc' := ho.trans hh.2.1
    have hsc := hs.1.trans hso
    have hsc' := hso.trans hs.2.1
    have hsign := hsq.2.1
    simp only [diff, sq, here, shifted, sub_nonneg, sub_nonpos] at hsign
    simp [check, bounds, cellInputBox,
      hh.1, hh.2.1, hh.2.2, hs.1, hs.2.1, hs.2.2,
      ho, hso, hhc, hhc', hsc, hsc', here, shifted, diff, sq,
      hsq.1, hsq.2.2.1, hsq.2.2.2, hsign, hd, two_mul]
    exact add_le_add hsq.1 hsq.1
  apply decide_eq_true
  simp only [canonicalCellAccepted, hcell]
  refine ⟨hR, hab, hc _, hc _, hc _, hc _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnorm⟩
  all_goals norm_num [unitPolynomialPayload, coefficientsOfExpr, evenizedCoefficients,
    coefficientAdd, coefficientNegArgument, check]

#print axioms check_unitPolynomialPayload

theorem unitPolynomialPayloads_cells_accepted (R : Nat) (hR : 0 < R)
    (s : Rat) (d m : Nat) :
    let payloads := unitPolynomialPayloads R s d m (4 * m + 4)
    payloads.length + 1 = (canonicalPoints R s d).length ∧
    (canonicalPoints R s d)[0]? = some (supportHullLower R s) ∧
    (canonicalPoints R s d)[payloads.length]? = some (supportHullUpper R s) ∧
    (∀ i, i < payloads.length →
      ∀ a b, cellAt R s d i = some (a, b) →
        payloads.getD i defaultPayload = unitPolynomialPayload R a b s m (4 * m + 4)) ∧
    (∀ i, i < payloads.length →
      checkCanonicalCell R [1] [1] s d i m (4 * m + 4)
        (payloads.getD i defaultPayload) = true) ∧
    (List.range payloads.length).all (fun i =>
      checkCanonicalCell R [1] [1] s d i m (4 * m + 4)
        (payloads.getD i defaultPayload)) = true := by
  dsimp only
  let payloads := unitPolynomialPayloads R s d m (4 * m + 4)
  have hlen : payloads.length = (sourceCells R s d).length := by
    simp [payloads, unitPolynomialPayloads]
  have hcount : payloads.length + 1 = (canonicalPoints R s d).length := by
    rw [hlen]
    exact sourceCells_length_add_one R s d
  have halign (i : Nat) (hi : i < payloads.length) (a b : Rat)
      (hcell : cellAt R s d i = some (a, b)) :
      payloads.getD i defaultPayload = unitPolynomialPayload R a b s m (4 * m + 4) := by
    have hindex := sourceCells_index R s d i (by omega)
    rw [hcell] at hindex
    simp [payloads, unitPolynomialPayloads, List.getD_eq_getElem?_getD,
      List.getElem?_map, hindex]
  have hchecks (i : Nat) (hi : i < payloads.length) :
      checkCanonicalCell R [1] [1] s d i m (4 * m + 4)
        (payloads.getD i defaultPayload) = true := by
    have hj : i + 1 < (canonicalPoints R s d).length := by omega
    have hcell := (show cellAt R s d i = some ((canonicalPoints R s d)[i],
        (canonicalPoints R s d)[i + 1]) from by
        simp [cellAt, List.getElem?_eq_getElem, hj,
          show i < (canonicalPoints R s d).length by omega])
    rw [halign i hi _ _ hcell]
    exact check_unitPolynomialPayload R hR s d i m _ _ hcell
  refine ⟨hcount, canonicalPoints_first R s d, ?_, halign, hchecks, ?_⟩
  · have hn : payloads.length = (canonicalPoints R s d).length - 1 := by omega
    rw [hn]
    exact canonicalPoints_last R s d
  · rw [List.all_eq_true]
    intro i hi
    exact hchecks i (List.mem_range.mp hi)

#print axioms unitPolynomialPayloads_cells_accepted

end D5.S3.Weil.Separator.TranslationEnergy
