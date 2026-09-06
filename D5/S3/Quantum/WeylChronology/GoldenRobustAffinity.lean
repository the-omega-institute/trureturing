/- GID: D5/S3/Quantum/WeylChronology/GoldenRobustAffinity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:cross-library-adapter)
   anchors: []
   digest: A nonnegative robust Ramsey margin gives an explicit Bhattacharyya affinity ceiling for the one-shot chronology laws. -/

import D5.S3.Quantum.WeylChronology.GoldenRobustLawSeparation
import D5.S3.TotalVariation.BhattacharyyaVariationMargin

/-!
# Robust chronology affinity

The calibration lane supplies a deterministic nominal-gap-minus-error margin.
The robust law adapter identifies that margin as a lower bound on total
variation. The generic variation-margin theorem then converts it into a
Bhattacharyya affinity ceiling. No new probability inequality appears here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenRobustAffinity

open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
open D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
open D5.S3.Quantum.WeylChronology.GoldenRobustLawSeparation
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.BhattacharyyaVariationMargin

noncomputable section

/-- The certified deterministic separation margin after subtracting both
calibration budgets from the nominal fringe gap. -/
def robustSeparationMargin
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool) : ℝ :=
  |visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right| -
    calibrationDeviationBudget leftCal v0 k0 left -
    calibrationDeviationBudget rightCal v0 k0 right

/-- A nonnegative robust separation margin yields an explicit one-shot
affinity ceiling. -/
theorem robust_bhattacharyya_le_margin_ceiling
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 ≤ robustSeparationMargin leftCal rightCal v0 k0 left right) :
    bhattacharyya
        (robustChronologyLaw leftCal left)
        (robustChronologyLaw rightCal right) ≤
      Real.sqrt
        (1 - robustSeparationMargin leftCal rightCal v0 k0 left right ^ 2) := by
  have hp := robust_chronology_probability_data
    leftCal left hleft0 hleft1
  have hq := robust_chronology_probability_data
    rightCal right hright0 hright1
  have htv :
      robustSeparationMargin leftCal rightCal v0 k0 left right ≤
        D5.S3.TotalVariation.Pinsker.totalVariation
          (robustChronologyLaw leftCal left)
          (robustChronologyLaw rightCal right) := by
    simpa [robustSeparationMargin] using
      (robust_total_variation_lower_bound leftCal rightCal v0 k0 left right)
  exact bhattacharyya_le_sqrt_one_sub_margin_sq
    (robustChronologyLaw leftCal left)
    (robustChronologyLaw rightCal right)
    hp hq (robustSeparationMargin leftCal rightCal v0 k0 left right)
    hmargin htv

#print axioms robust_bhattacharyya_le_margin_ceiling

end
end D5.S3.Quantum.WeylChronology.GoldenRobustAffinity
