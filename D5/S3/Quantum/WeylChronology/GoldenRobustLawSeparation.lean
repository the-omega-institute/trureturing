/- GID: D5/S3/Quantum/WeylChronology/GoldenRobustLawSeparation
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:cross-library-adapter)
   anchors: []
   digest: Robust fringe margins become exact total-variation margins for the canonical finite-shot Bool law. -/

import D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
import D5.S3.TotalVariation.Asymptotics.BernoulliBiasPairDistance

/-!
# Robust law separation

The calibration module stops at a deterministic plus-port probability gap.
The generic Bernoulli adapter proves that this gap is exactly total variation
for the repository's canonical Bool law. This file performs only that
transport. It introduces no new testing inequality or concentration theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenRobustLawSeparation

open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
open D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData
open D5.S3.TotalVariation.Asymptotics.BernoulliBiasPairDistance
open D5.S3.TotalVariation.Pinsker

noncomputable section

/-- Canonical Bool law associated with one robust plus-port probability. -/
def robustChronologyLaw
    (cal : RamseyCalibration) (word : List Bool) : Bool → ℝ :=
  positiveBiasLaw (robustChronologyFringe cal word - 1 / 2)

/-- A robust fringe in the unit interval gives honest probability data. -/
theorem robust_chronology_probability_data
    (cal : RamseyCalibration) (word : List Bool)
    (h0 : 0 ≤ robustChronologyFringe cal word)
    (h1 : robustChronologyFringe cal word ≤ 1) :
    (∀ b, 0 ≤ robustChronologyLaw cal word b) ∧
      ∑ b, robustChronologyLaw cal word b = 1 := by
  have hbias : |robustChronologyFringe cal word - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  simpa [robustChronologyLaw] using (bias_laws_probability_data hbias).1

/-- Total variation between two robust one-shot laws is exactly their actual
plus-port probability gap. -/
theorem robust_law_total_variation
    (leftCal rightCal : RamseyCalibration) (left right : List Bool) :
    totalVariation
        (robustChronologyLaw leftCal left)
        (robustChronologyLaw rightCal right) =
      |robustChronologyFringe leftCal left -
        robustChronologyFringe rightCal right| := by
  unfold robustChronologyLaw
  exact plus_probability_pair_total_variation
    (robustChronologyFringe leftCal left)
    (robustChronologyFringe rightCal right)

/-- The deterministic calibration margin is also a certified lower bound on
one-shot total variation. -/
theorem robust_total_variation_lower_bound
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool) :
    |visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right| -
        calibrationDeviationBudget leftCal v0 k0 left -
        calibrationDeviationBudget rightCal v0 k0 right ≤
      totalVariation
        (robustChronologyLaw leftCal left)
        (robustChronologyLaw rightCal right) := by
  rw [robust_law_total_variation]
  exact robust_pair_separation_lower_bound leftCal rightCal v0 k0 left right

/-- If the nominal gap exceeds both calibration budgets, the robust one-shot
laws have strictly positive total variation. -/
theorem robust_total_variation_pos_of_nominal_margin
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hmargin : calibrationDeviationBudget leftCal v0 k0 left +
        calibrationDeviationBudget rightCal v0 k0 right <
      |visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right|) :
    0 < totalVariation
      (robustChronologyLaw leftCal left)
      (robustChronologyLaw rightCal right) := by
  have h := robust_total_variation_lower_bound
    leftCal rightCal v0 k0 left right
  linarith

#print axioms robust_chronology_probability_data
#print axioms robust_law_total_variation
#print axioms robust_total_variation_lower_bound
#print axioms robust_total_variation_pos_of_nominal_margin

end
end D5.S3.Quantum.WeylChronology.GoldenRobustLawSeparation
