/- GID: D5/S3/Quantum/WeylChronology/GoldenRobustShotComplexity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:cross-library-adapter)
   anchors: []
   digest: A positive certified robust Ramsey margin gives a positive exponential discrimination rate and an explicit sufficient shot-count inequality for target Bayes risk. -/

import D5.S3.Quantum.WeylChronology.GoldenRobustFiniteShot
import D5.S3.TotalVariation.IndependentSamplingExponentialBound
import D5.S3.TotalVariation.Metric

/-!
# Robust Ramsey shot complexity

The sharp finite-suite adapter gives

`e_N^* <= (sqrt (1 - delta^2))^N / 2`

for the certified robust separation margin `delta`. The repository already
owns the elementary independent-sampling envelope

`(1-epsilon)^N <= exp (-epsilon*N)`.

Taking `epsilon = 1 - sqrt (1-delta^2)` produces a positive rate whenever the
robust margin is strictly positive. This yields both an exponential risk bound
and a direct sufficient real-valued shot-count threshold for a target risk.
The preceding representation bridge means the same operational optimum also
controls every recursive iid decision event after exact reindexing.

No asymptotic approximation, Chernoff optimization, concentration inequality,
or integer rounding convention is introduced here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenRobustShotComplexity

open D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
open D5.S3.Quantum.WeylChronology.GoldenRobustLawSeparation
open D5.S3.Quantum.WeylChronology.GoldenRobustAffinity
open D5.S3.Quantum.WeylChronology.GoldenRobustFiniteShot
open D5.S3.TotalVariation.IndependentSamplingExponentialBound
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

noncomputable section

/-- Exponential finite-shot rate induced by the robust one-shot affinity
ceiling. -/
def robustShotRate
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool) : ℝ :=
  1 - Real.sqrt
    (1 - robustSeparationMargin leftCal rightCal v0 k0 left right ^ 2)

/-- Every certified robust margin between valid probability laws is at most
one, because it is bounded by total variation. -/
theorem robust_separation_margin_le_one
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1) :
    robustSeparationMargin leftCal rightCal v0 k0 left right ≤ 1 := by
  have hp := robust_chronology_probability_data leftCal left hleft0 hleft1
  have hq := robust_chronology_probability_data rightCal right hright0 hright1
  have hlower :
      robustSeparationMargin leftCal rightCal v0 k0 left right ≤
        totalVariation
          (robustChronologyLaw leftCal left)
          (robustChronologyLaw rightCal right) := by
    simpa [robustSeparationMargin] using
      (robust_total_variation_lower_bound leftCal rightCal v0 k0 left right)
  exact hlower.trans
    (total_variation_le_one
      (robustChronologyLaw leftCal left)
      (robustChronologyLaw rightCal right) hp hq)

/-- Under a nonnegative certified margin, the induced exponential rate lies in
the unit interval. -/
theorem robust_shot_rate_mem_unit
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 ≤ robustSeparationMargin leftCal rightCal v0 k0 left right) :
    0 ≤ robustShotRate leftCal rightCal v0 k0 left right ∧
      robustShotRate leftCal rightCal v0 k0 left right ≤ 1 := by
  let delta := robustSeparationMargin leftCal rightCal v0 k0 left right
  have hdeltaNonnegative : 0 ≤ delta := by
    simpa [delta] using hmargin
  have hdeltaOne : delta ≤ 1 :=
    robust_separation_margin_le_one leftCal rightCal v0 k0 left right
      hleft0 hleft1 hright0 hright1
  have hradNonnegative : 0 ≤ 1 - delta ^ 2 := by
    nlinarith
  have hradAtMostOne : 1 - delta ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg delta]
  have hrootNonnegative : 0 ≤ Real.sqrt (1 - delta ^ 2) := Real.sqrt_nonneg _
  have hrootSquare : Real.sqrt (1 - delta ^ 2) ^ 2 = 1 - delta ^ 2 :=
    Real.sq_sqrt hradNonnegative
  have hrootAtMostOne : Real.sqrt (1 - delta ^ 2) ≤ 1 := by
    nlinarith
  change 0 ≤ 1 - Real.sqrt (1 - delta ^ 2) ∧
    1 - Real.sqrt (1 - delta ^ 2) ≤ 1
  constructor <;> linarith

/-- A strictly positive robust margin gives a strictly positive exponential
shot rate. -/
theorem robust_shot_rate_pos_of_margin_pos
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 < robustSeparationMargin leftCal rightCal v0 k0 left right) :
    0 < robustShotRate leftCal rightCal v0 k0 left right := by
  let delta := robustSeparationMargin leftCal rightCal v0 k0 left right
  have hdeltaPositive : 0 < delta := by
    simpa [delta] using hmargin
  have hdeltaOne : delta ≤ 1 :=
    robust_separation_margin_le_one leftCal rightCal v0 k0 left right
      hleft0 hleft1 hright0 hright1
  have hradNonnegative : 0 ≤ 1 - delta ^ 2 := by
    nlinarith
  have hrootNonnegative : 0 ≤ Real.sqrt (1 - delta ^ 2) := Real.sqrt_nonneg _
  have hrootSquare : Real.sqrt (1 - delta ^ 2) ^ 2 = 1 - delta ^ 2 :=
    Real.sq_sqrt hradNonnegative
  have hdeltaSquarePositive : 0 < delta ^ 2 := sq_pos_of_pos hdeltaPositive
  have hradStrict : 1 - delta ^ 2 < 1 := by
    nlinarith
  have hrootStrict : Real.sqrt (1 - delta ^ 2) < 1 := by
    nlinarith
  change 0 < 1 - Real.sqrt (1 - delta ^ 2)
  linarith

/-- The sharp affinity-power risk bound admits a simpler exponential envelope
with rate `robustShotRate`. -/
theorem robust_repeated_optimal_error_le_exponential_rate
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 ≤ robustSeparationMargin leftCal rightCal v0 k0 left right)
    (shots : ℕ) :
    robustRepeatedOptimalError leftCal rightCal left right shots ≤
      Real.exp (-(robustShotRate leftCal rightCal v0 k0 left right *
        (shots : ℝ))) / 2 := by
  have hrate := robust_shot_rate_mem_unit
    leftCal rightCal v0 k0 left right
    hleft0 hleft1 hright0 hright1 hmargin
  have hpower := robust_repeated_optimal_error_le_margin_power
    leftCal rightCal v0 k0 left right
    hleft0 hleft1 hright0 hright1 hmargin shots
  have hexponential := independent_sampling_exponential_bound
    (robustShotRate leftCal rightCal v0 k0 left right)
    shots hrate.1 hrate.2
  have honeSub :
      1 - robustShotRate leftCal rightCal v0 k0 left right =
        Real.sqrt
          (1 - robustSeparationMargin leftCal rightCal v0 k0 left right ^ 2) := by
    simp [robustShotRate]
  rw [honeSub] at hexponential
  nlinarith

/-- Logarithmic evidence budget sufficient for a target equal-prior Bayes risk. -/
theorem robust_repeated_target_error_of_log_budget
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 ≤ robustSeparationMargin leftCal rightCal v0 k0 left right)
    (shots : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hbudget :
      Real.log (1 / (2 * eps)) ≤
        robustShotRate leftCal rightCal v0 k0 left right * (shots : ℝ)) :
    robustRepeatedOptimalError leftCal rightCal left right shots ≤ eps := by
  have hupper := robust_repeated_optimal_error_le_exponential_rate
    leftCal rightCal v0 k0 left right
    hleft0 hleft1 hright0 hright1 hmargin shots
  have hneg :
      -(robustShotRate leftCal rightCal v0 k0 left right * (shots : ℝ)) ≤
        -Real.log (1 / (2 * eps)) := by
    linarith
  have hexp := Real.exp_le_exp_of_le hneg
  have hpositive : 0 < 1 / (2 * eps) := by positivity
  have heval : Real.exp (-Real.log (1 / (2 * eps))) = 2 * eps := by
    rw [Real.exp_neg, Real.exp_log hpositive]
    simp [one_div]
  rw [heval] at hexp
  nlinarith

/-- Explicit sufficient real-valued shot-count threshold. A strictly positive
robust margin automatically gives the positive rate needed to divide by it. -/
theorem robust_repeated_target_error_of_shot_count
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 < robustSeparationMargin leftCal rightCal v0 k0 left right)
    (shots : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hshots :
      Real.log (1 / (2 * eps)) /
          robustShotRate leftCal rightCal v0 k0 left right ≤
        (shots : ℝ)) :
    robustRepeatedOptimalError leftCal rightCal left right shots ≤ eps := by
  have hrate : 0 < robustShotRate leftCal rightCal v0 k0 left right :=
    robust_shot_rate_pos_of_margin_pos
      leftCal rightCal v0 k0 left right
      hleft0 hleft1 hright0 hright1 hmargin
  have hbudget :
      Real.log (1 / (2 * eps)) ≤
        robustShotRate leftCal rightCal v0 k0 left right * (shots : ℝ) := by
    have h := (div_le_iff₀ hrate).mp hshots
    simpa [mul_comm] using h
  exact robust_repeated_target_error_of_log_budget
    leftCal rightCal v0 k0 left right
    hleft0 hleft1 hright0 hright1 hmargin.le
    shots eps heps hbudget

#print axioms robust_separation_margin_le_one
#print axioms robust_shot_rate_mem_unit
#print axioms robust_shot_rate_pos_of_margin_pos
#print axioms robust_repeated_optimal_error_le_exponential_rate
#print axioms robust_repeated_target_error_of_log_budget
#print axioms robust_repeated_target_error_of_shot_count

end
end D5.S3.Quantum.WeylChronology.GoldenRobustShotComplexity
