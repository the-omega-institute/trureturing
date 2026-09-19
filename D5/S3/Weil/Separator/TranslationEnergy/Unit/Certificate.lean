/- GID: D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Unit/Certificate
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=certified-instance; basis=terminal=gid:D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.log_two_certificate
   digest: Certify one exact nonzero translation-energy box and transfer it to log two. -/

import D5.S3.Weil.Separator.TranslationEnergy.Unit.Width
import D5.S3.Weil.Separator.TranslationEnergy.UnitLowerBound
import D5.S3.Weil.Separator.LiteralRationalPrimeTranslationBound
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Separator.TranslationEnergy.Unit

open Polynomial
open D5.S3.Weil.Separator.TranslationEnergy
open D5.S3.Weil.Separator.TranslationEnergy.UnitLowerBound
open D5.S3.Weil.Separator.TranslationEnergy.LiteralFunction
open D5.S3.Weil.Separator.LiteralRationalPrimeTranslationBound
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

def centerShift : Rat := 287209 / 414355

def centerPayloads : List CanonicalCellPayload :=
  unitPolynomialPayloads 1 centerShift 15 16 (4 * 16 + 4)

def centerBox : Rat × Rat := aggregateBounds 1 centerShift 15 centerPayloads

def logTwoBox : Rat × Rat :=
  (centerBox.1 - 1152 / (10 ^ 10 : Rat),
    centerBox.2 + 1152 / (10 ^ 10 : Rat))

/-- The full canonical producer, rather than a selected cell, yields a
strictly narrow rational enclosure of the literal unit test's translation
energy, with an independently lower-bounded positive value. -/
theorem center_certificate :
    unitLiteral 0 = (1 : Complex) + Complex.I ∧
    checkFull 1 [1] [1] centerShift 15 16 (4 * 16 + 4) 4 centerPayloads = true ∧
    (centerBox.1 : Real) ≤ translationEnergy unitLiteral centerShift ∧
    translationEnergy unitLiteral centerShift ≤ (centerBox.2 : Real) ∧
    0 < centerBox.1 ∧ centerBox.2 - centerBox.1 ≤
      (115 / 2048 + 5 / 268435456 : Rat) := by
  have hwidth : centerBox.2 - centerBox.1 ≤
      (115 / 2048 + 5 / 268435456 : Rat) := by
    have hw := unit_aggregate_width 1 (by decide) centerShift 15 16
    change centerBox.2 - centerBox.1 ≤ _ at *
    calc
      centerBox.2 - centerBox.1 ≤
          72 / (1 : Rat) *
            (((supportHullUpper 1 centerShift - supportHullLower 1 centerShift) /
              ((2 ^ 15 : Nat) : Rat)) *
              (supportHullUpper 1 centerShift - supportHullLower 1 centerShift)) +
            (16 * (1 / 2 : Rat) ^ 16 + 16 / (2 ^ 32 : Rat)) *
              (supportHullUpper 1 centerShift - supportHullLower 1 centerShift) := hw
      _ ≤ (115 / 2048 + 5 / 268435456 : Rat) := by
        norm_num [centerShift, supportHullUpper, supportHullLower]
  have hacc := unitPolynomialPayloads_cells_accepted 1 (by decide) centerShift 15 16
  have hfull : checkFull 1 [1] [1] centerShift 15 16
      (4 * 16 + 4) 4 centerPayloads = true := by
    apply decide_eq_true
    refine ⟨by decide, hacc.1, hacc.2.1, hacc.2.2.1,
      hacc.2.2.2.2.2, ?_⟩
    exact hwidth.trans (by norm_num)
  have hfun (y : Real) :
      unitLiteral y =
        ((Real.smoothTransition (2 - |y| / (1 : Nat)) : Real) : Complex) *
          rationalEvenPolynomial (C 1 : Rat[X]) (C 1 : Rat[X]) y := by
    rfl
  have hs := checked_literal_translation_energy_sound 1 (C 1) (C 1)
    centerShift [1] [1] (by simp [coefficientPolynomial])
    (by simp [coefficientPolynomial]) 15 16 (4 * 16 + 4) 4 centerPayloads
    hfull unitLiteral hfun
  have hshift : (5 / 8 : Real) ≤ (centerShift : Real) ∧
      (centerShift : Real) ≤ 1 := by norm_num [centerShift]
  have hlower := unit_literal_translationEnergy_lower (centerShift : Real)
    hshift.1 hshift.2
  have hnarrow : centerBox.2 - centerBox.1 < (1 / 16 : Rat) :=
    lt_of_le_of_lt hwidth (by norm_num)
  have hpositive : 0 < centerBox.1 := by
    have hw : (centerBox.2 : Real) - centerBox.1 < 1 / 16 := by
      have hh : ((centerBox.2 - centerBox.1 : Rat) : Real) < (1 / 16 : Real) := by
        simpa using (Rat.cast_lt (K := Real)).mpr hnarrow
      simpa only [Rat.cast_sub] using hh
    have hl : (1 / 16 : Real) ≤ (centerBox.2 : Real) :=
      hlower.trans hs.2.1
    exact_mod_cast (show (0 : Real) < centerBox.1 by linarith)
  have hzero : unitLiteral 0 = (1 : Complex) + Complex.I := by
    rw [hfun 0]
    norm_num [rationalEvenPolynomial,
      Real.smoothTransition.one_of_one_le (show (1 : Real) ≤ 2 by norm_num)]
  exact ⟨hzero, hfull, hs.1, hs.2.1, hpositive, hwidth⟩

/-- The same exact literal Weil test at the actual logarithmic prime shift is
enclosed after a two-sided rational inflation of the certified center box. -/
theorem log_two_certificate :
    unitLiteral 0 = (1 : Complex) + Complex.I ∧
    checkFull 1 [1] [1] centerShift 15 16 (4 * 16 + 4) 4 centerPayloads = true ∧
    (logTwoBox.1 : Real) ≤ translationEnergy unitLiteral (Real.log 2) ∧
    translationEnergy unitLiteral (Real.log 2) ≤ (logTwoBox.2 : Real) ∧
    0 < logTwoBox.1 ∧ logTwoBox.2 - logTwoBox.1 < (1 / 16 : Rat) := by
  have hc := center_certificate
  have hfun (y : Real) :
      unitLiteral y =
        ((Real.smoothTransition (2 - |y| / (1 : Nat)) : Real) : Complex) *
          rationalEvenPolynomial (C 1 : Rat[X]) (C 1 : Rat[X]) y := by
    rfl
  have hmod := literal_rational_prime_translation_bound 1 (by decide)
    (C 1 : Rat[X]) (C 1 : Rat[X]) unitLiteral hfun (Real.log 2) (centerShift : Real)
  have hs : |Real.log 2 - (centerShift : Real)| ≤ (1 / 10 ^ 10 : Real) := by
    convert Real.log_two_near_10 using 1
    norm_num [centerShift]
  have hcoef :
      |translationEnergy unitLiteral (Real.log 2) -
          translationEnergy unitLiteral (centerShift : Real)| ≤
        (1152 / (10 ^ 10 : Rat) : Real) := by
    calc
      _ ≤ (1152 : Real) * |Real.log 2 - (centerShift : Real)| := by
        convert hmod using 1
        norm_num [coefficientBudget]
      _ ≤ 1152 * (1 / 10 ^ 10 : Real) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = (1152 / (10 ^ 10 : Rat) : Real) := by norm_num
  have hw : logTwoBox.2 - logTwoBox.1 < (1 / 16 : Rat) := by
    dsimp [logTwoBox]
    have hcWidth := hc.2.2.2.2.2
    linarith [show (115 / 2048 + 5 / 268435456 : Rat) +
      2304 / (10 ^ 10 : Rat) < 1 / 16 by norm_num]
  have hlogRange : (5 / 8 : Real) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
    have hd : |Real.log 2 - (centerShift : Real)| ≤ (1 / 10 ^ 10 : Real) := hs
    rw [abs_le] at hd
    constructor <;> norm_num [centerShift] at * <;> linarith
  have hpos : 0 < logTwoBox.1 := by
    have he := unit_literal_translationEnergy_lower (Real.log 2)
      hlogRange.1 hlogRange.2
    have hr : translationEnergy unitLiteral (Real.log 2) ≤
        (logTwoBox.2 : Real) := by
      have hdelta := (abs_le.mp hcoef).2
      dsimp [logTwoBox]
      push_cast
      linarith [hc.2.2.2.1]
    have hwR : (logTwoBox.2 : Real) - logTwoBox.1 < 1 / 16 := by
      have hh : ((logTwoBox.2 - logTwoBox.1 : Rat) : Real) < (1 / 16 : Real) := by
        simpa using (Rat.cast_lt (K := Real)).mpr hw
      simpa only [Rat.cast_sub] using hh
    exact_mod_cast (show (0 : Real) < logTwoBox.1 by linarith)
  have hle : (logTwoBox.1 : Real) ≤ translationEnergy unitLiteral (Real.log 2) := by
    have hd := (abs_le.mp hcoef).1
    dsimp [logTwoBox]
    push_cast
    linarith [hc.2.2.1]
  have hge : translationEnergy unitLiteral (Real.log 2) ≤ (logTwoBox.2 : Real) := by
    have hd := (abs_le.mp hcoef).2
    dsimp [logTwoBox]
    push_cast
    linarith [hc.2.2.2.1]
  exact ⟨hc.1, hc.2.1, hle, hge, hpos, hw⟩

#print axioms center_certificate
#print axioms log_two_certificate

end D5.S3.Weil.Separator.TranslationEnergy.Unit
