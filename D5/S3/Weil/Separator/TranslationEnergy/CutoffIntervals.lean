/- GID: D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/CutoffIntervals
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Compute quantitative cutoff enclosures on shifted rational cells. -/

import D5.S3.Weil.Separator.TranslationEnergy.Scalar.Uniform
import D5.S3.Weil.Separator.LiteralRationalPrimeTranslationBound
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

namespace D5.S3.Weil.Separator.TranslationEnergy.CutoffIntervals

open D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic
open D5.S3.Weil.Separator.TranslationEnergy.Scalar.Uniform
open private smoothTransition_lipschitz from
  D5.S3.Weil.Separator.LiteralRationalPrimeTranslationBound

/-- A computable enclosure using the lower endpoint's lower scalar bound and the
upper endpoint's upper scalar bound. -/
def cutoffInterval (ta tb : Rat) (m : Nat) : Rat × Rat :=
  ((cutoffLogisticInterval ta m (4 * m + 4)).1,
    (cutoffLogisticInterval tb m (4 * m + 4)).2)

/-- The minimum absolute value attained on the rational shifted interval. -/
def shiftedMinAbs (a b c : Rat) : Rat :=
  if a + c ≤ 0 ∧ 0 ≤ b + c then 0 else min |a + c| |b + c|

/-- The maximum absolute value attained on the rational shifted interval. -/
def shiftedMaxAbs (a b c : Rat) : Rat := max |a + c| |b + c|

/-- Lower cutoff parameter on a shifted spatial interval. -/
def shiftedCutoffArgLower (r a b c : Rat) : Rat :=
  2 - shiftedMaxAbs a b c / r

/-- Upper cutoff parameter on a shifted spatial interval. -/
def shiftedCutoffArgUpper (r a b c : Rat) : Rat :=
  2 - shiftedMinAbs a b c / r

/-- The computable cutoff enclosure for `2 - |x + c| / r` on `[a,b]`. -/
def shiftedCutoffInterval (r a b c : Rat) (m : Nat) : Rat × Rat :=
  cutoffInterval (shiftedCutoffArgLower r a b c)
    (shiftedCutoffArgUpper r a b c) m

private theorem shifted_abs_mem (a b c : Rat) (x : Real)
    (hx : (a : Real) ≤ x ∧ x ≤ (b : Real)) :
    (shiftedMinAbs a b c : Real) ≤ |x + c| ∧
      |x + c| ≤ (shiftedMaxAbs a b c : Real) := by
  have hlo : ((a + c : Rat) : Real) ≤ x + c := by
    push_cast
    linarith
  have hhi : x + c ≤ ((b + c : Rat) : Real) := by
    push_cast
    linarith
  constructor
  · simp only [shiftedMinAbs]
    split_ifs with hcross
    · simp
    · by_cases ha0 : a + c ≤ 0
      · have hb0 : b + c ≤ 0 := le_of_not_ge fun hb0 => hcross ⟨ha0, hb0⟩
        rw [Rat.cast_min, Rat.cast_abs, Rat.cast_abs,
          abs_of_nonpos (show ((a + c : Rat) : Real) ≤ 0 by exact_mod_cast ha0),
          abs_of_nonpos (show ((b + c : Rat) : Real) ≤ 0 by exact_mod_cast hb0),
          abs_of_nonpos (hhi.trans (show ((b + c : Rat) : Real) ≤ 0 by
            exact_mod_cast hb0))]
        exact min_le_right _ _ |>.trans (neg_le_neg hhi)
      · have ha0' : 0 ≤ a + c := le_of_not_ge ha0
        rw [Rat.cast_min, Rat.cast_abs, Rat.cast_abs,
          abs_of_nonneg (show (0 : Real) ≤ ((a + c : Rat) : Real) by
            exact_mod_cast ha0'),
          abs_of_nonneg ((show (0 : Real) ≤ ((a + c : Rat) : Real) by
            exact_mod_cast ha0').trans hlo)]
        exact min_le_left _ _ |>.trans hlo
  · simpa only [shiftedMaxAbs, Rat.cast_max, Rat.cast_abs, Rat.cast_add] using
      abs_le_max_abs_abs hlo hhi

private theorem shifted_abs_range (a b c : Rat) (hab : a ≤ b) :
    shiftedMinAbs a b c ≤ shiftedMaxAbs a b c ∧
      shiftedMaxAbs a b c - shiftedMinAbs a b c ≤ b - a := by
  have hab' : a + c ≤ b + c := by linarith
  by_cases hcross : a + c ≤ 0 ∧ 0 ≤ b + c
  · rcases hcross with ⟨ha0, hb0⟩
    have hla : |a + c| ≤ b - a := by rw [abs_of_nonpos ha0]; linarith
    have hlb : |b + c| ≤ b - a := by rw [abs_of_nonneg hb0]; linarith
    simp only [shiftedMinAbs, shiftedMaxAbs, ha0, hb0, and_self, if_true,
      sub_zero]
    exact ⟨le_max_of_le_left (abs_nonneg _), max_le hla hlb⟩
  · by_cases ha0 : a + c ≤ 0
    · have hb0 : b + c ≤ 0 := le_of_not_ge fun hb0 => hcross ⟨ha0, hb0⟩
      have habs : |b + c| ≤ |a + c| := by
        rw [abs_of_nonpos ha0, abs_of_nonpos hb0]
        linarith
      simp only [shiftedMinAbs, shiftedMaxAbs, hcross, if_false]
      rw [min_eq_right habs, max_eq_left habs, abs_of_nonpos ha0,
        abs_of_nonpos hb0]
      constructor <;> linarith
    · have ha0' : 0 ≤ a + c := le_of_not_ge ha0
      have hb0 : 0 ≤ b + c := ha0'.trans hab'
      have habs : |a + c| ≤ |b + c| := by
        rw [abs_of_nonneg ha0', abs_of_nonneg hb0]
        exact hab'
      simp only [shiftedMinAbs, shiftedMaxAbs, hcross, if_false]
      rw [min_eq_left habs, max_eq_right habs, abs_of_nonneg ha0',
        abs_of_nonneg hb0]
      constructor <;> linarith

/-- Generic endpoint certificates produce a sound interval throughout a rational
parameter cell, with variation charged to the global cutoff modulus. -/
theorem cutoffInterval_certificate (ta tb : Rat) (m : Nat) (ht : ta ≤ tb) :
    checkCutoffLogistic ta m (4 * m + 4) = true ∧
    checkCutoffLogistic tb m (4 * m + 4) = true ∧
    0 ≤ (cutoffInterval ta tb m).1 ∧
    (cutoffInterval ta tb m).1 ≤ (cutoffInterval ta tb m).2 ∧
    (cutoffInterval ta tb m).2 ≤ 1 ∧
    (∀ t : Real, (ta : Real) ≤ t → t ≤ (tb : Real) →
      ((cutoffInterval ta tb m).1 : Real) ≤ Real.smoothTransition t ∧
      Real.smoothTransition t ≤ ((cutoffInterval ta tb m).2 : Real)) ∧
    (cutoffInterval ta tb m).2 - (cutoffInterval ta tb m).1 ≤
      9 * (tb - ta) + 2 * (1 / 2 : Rat) ^ m := by
  let aBox := cutoffLogisticInterval ta m (4 * m + 4)
  let bBox := cutoffLogisticInterval tb m (4 * m + 4)
  have ha := checkCutoffLogistic_all_precision ta m
  have hb := checkCutoffLogistic_all_precision tb m
  have has := checked_cutoff_logistic_sound ta m (4 * m + 4) ha.1
  have hbs := checked_cutoff_logistic_sound tb m (4 * m + 4) hb.1
  have htr : (ta : Real) ≤ (tb : Real) := by exact_mod_cast ht
  have hmono : Real.smoothTransition (ta : Real) ≤ Real.smoothTransition (tb : Real) :=
    Real.smoothTransition.monotone htr
  have hlip := smoothTransition_lipschitz (ta : Real) (tb : Real)
  have hdist : |(ta : Real) - (tb : Real)| = (tb : Real) - (ta : Real) := by
    rw [abs_of_nonpos (sub_nonpos.mpr htr)]
    ring
  rw [hdist] at hlip
  rw [abs_of_nonpos (sub_nonpos.mpr hmono)] at hlip
  have hvariation : Real.smoothTransition (tb : Real) -
      Real.smoothTransition (ta : Real) ≤ 9 * ((tb : Real) - (ta : Real)) := by
    linarith [hlip]
  have hwidthR : ((bBox.2 - aBox.1 : Rat) : Real) ≤
      ((9 * (tb - ta) + 2 * (1 / 2 : Rat) ^ m : Rat) : Real) := by
    have haWidth : ((aBox.2 - aBox.1 : Rat) : Real) ≤
        (((1 / 2 : Rat) ^ m : Rat) : Real) := by exact_mod_cast ha.2.2.2.2
    have hbWidth : ((bBox.2 - bBox.1 : Rat) : Real) ≤
        (((1 / 2 : Rat) ^ m : Rat) : Real) := by exact_mod_cast hb.2.2.2.2
    have haErr : Real.smoothTransition (ta : Real) - (aBox.1 : Real) ≤
        (((1 / 2 : Rat) ^ m : Rat) : Real) := by
      exact (sub_le_sub_right has.2.2.1 (aBox.1 : Real)).trans (by
        simpa only [Rat.cast_sub] using haWidth)
    have hbErr : (bBox.2 : Real) - Real.smoothTransition (tb : Real) ≤
        (((1 / 2 : Rat) ^ m : Rat) : Real) := by
      exact (sub_le_sub_left hbs.2.1 (bBox.2 : Real)).trans (by
        simpa only [Rat.cast_sub] using hbWidth)
    calc
      ((bBox.2 - aBox.1 : Rat) : Real) =
          ((bBox.2 : Rat) : Real) - Real.smoothTransition (tb : Real) +
            (Real.smoothTransition (tb : Real) - Real.smoothTransition (ta : Real)) +
            (Real.smoothTransition (ta : Real) - ((aBox.1 : Rat) : Real)) := by
              push_cast
              ring
      _ ≤ (((1 / 2 : Rat) ^ m : Rat) : Real) +
          9 * ((tb : Real) - (ta : Real)) +
          (((1 / 2 : Rat) ^ m : Rat) : Real) :=
        add_le_add (add_le_add hbErr hvariation) haErr
      _ = ((9 * (tb - ta) + 2 * (1 / 2 : Rat) ^ m : Rat) : Real) := by
        push_cast
        ring
  refine ⟨ha.1, hb.1, ha.2.1, ?_, hb.2.2.2.1, ?_, ?_⟩
  · have horderR : (aBox.1 : Real) ≤ (bBox.2 : Real) :=
      has.2.1.trans (hmono.trans hbs.2.2.1)
    exact_mod_cast horderR
  · intro t hta htb
    exact ⟨has.2.1.trans (Real.smoothTransition.monotone hta),
      (Real.smoothTransition.monotone htb).trans hbs.2.2.1⟩
  · exact_mod_cast hwidthR

/-- A positive rational radius yields a certified cutoff enclosure on every
shifted rational spatial cell, including a sharp parameter-range contribution. -/
theorem shiftedCutoffInterval_certificate (r a b c : Rat) (m : Nat)
    (hr : 0 < r) (hab : a ≤ b) :
    let ta := shiftedCutoffArgLower r a b c
    let tb := shiftedCutoffArgUpper r a b c
    ta ≤ tb ∧
    tb - ta ≤ (b - a) / r ∧
    checkCutoffLogistic ta m (4 * m + 4) = true ∧
    checkCutoffLogistic tb m (4 * m + 4) = true ∧
    0 ≤ (shiftedCutoffInterval r a b c m).1 ∧
    (shiftedCutoffInterval r a b c m).1 ≤
      (shiftedCutoffInterval r a b c m).2 ∧
    (shiftedCutoffInterval r a b c m).2 ≤ 1 ∧
    (∀ x : Real, (a : Real) ≤ x → x ≤ (b : Real) →
      ((shiftedCutoffInterval r a b c m).1 : Real) ≤
        Real.smoothTransition (2 - |x + c| / r) ∧
      Real.smoothTransition (2 - |x + c| / r) ≤
        ((shiftedCutoffInterval r a b c m).2 : Real)) ∧
    (shiftedCutoffInterval r a b c m).2 -
        (shiftedCutoffInterval r a b c m).1 ≤
      9 * ((b - a) / r) + 2 * (1 / 2 : Rat) ^ m := by
  dsimp only
  have habs := shifted_abs_range a b c hab
  have ht : shiftedCutoffArgLower r a b c ≤ shiftedCutoffArgUpper r a b c := by
    dsimp [shiftedCutoffArgLower, shiftedCutoffArgUpper]
    exact sub_le_sub_left (div_le_div_of_nonneg_right habs.1 hr.le) 2
  have hspan : shiftedCutoffArgUpper r a b c - shiftedCutoffArgLower r a b c ≤
      (b - a) / r := by
    dsimp [shiftedCutoffArgLower, shiftedCutoffArgUpper]
    calc
      (2 - shiftedMinAbs a b c / r) - (2 - shiftedMaxAbs a b c / r) =
          (shiftedMaxAbs a b c - shiftedMinAbs a b c) / r := by ring
      _ ≤ (b - a) / r := div_le_div_of_nonneg_right habs.2 hr.le
  have hcert := cutoffInterval_certificate
    (shiftedCutoffArgLower r a b c) (shiftedCutoffArgUpper r a b c) m ht
  refine ⟨ht, hspan, hcert.1, hcert.2.1, hcert.2.2.1,
    hcert.2.2.2.1, hcert.2.2.2.2.1, ?_, ?_⟩
  · intro x hax hxb
    have hxabs := shifted_abs_mem a b c x ⟨hax, hxb⟩
    have hrr : (0 : Real) < (r : Real) := by exact_mod_cast hr
    have harg : (shiftedCutoffArgLower r a b c : Real) ≤
        2 - |x + c| / r ∧
        2 - |x + c| / r ≤ (shiftedCutoffArgUpper r a b c : Real) := by
      dsimp [shiftedCutoffArgLower, shiftedCutoffArgUpper]
      push_cast
      constructor <;> apply sub_le_sub_left
      · exact div_le_div_of_nonneg_right hxabs.2 hrr.le
      · exact div_le_div_of_nonneg_right hxabs.1 hrr.le
    exact hcert.2.2.2.2.2.1 _ harg.1 harg.2
  · exact hcert.2.2.2.2.2.2.trans (by nlinarith [hspan])

#print axioms cutoffInterval_certificate
#print axioms shiftedCutoffInterval_certificate

end D5.S3.Weil.Separator.TranslationEnergy.CutoffIntervals
