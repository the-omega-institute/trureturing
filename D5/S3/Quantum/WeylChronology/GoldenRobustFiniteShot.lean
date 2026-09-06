/- GID: D5/S3/Quantum/WeylChronology/GoldenRobustFiniteShot
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:cross-library-adapter)
   anchors: []
   digest: A certified robust Ramsey margin controls the operational finite-shot Bayes risk, with exact transport between recursive iid tests and the Fin-indexed finite-suite representation. -/

import D5.S3.Quantum.WeylChronology.GoldenRobustAffinity
import D5.S3.Estimation.ErrorExponents.FiniteSuiteAffinityProductBound
import D5.S3.Estimation.ErrorExponents.FiniteRepetitionRepresentationEquiv

/-!
# Robust finite-shot chronology testing

The deterministic calibration layer supplies a residual separation margin.
The robust-law layer turns that margin into total variation, and the affinity
layer turns it into the one-shot ceiling

`sqrt (1 - margin^2)`.

This module feeds that ceiling into the repository's operational finite
independent-suite Bayes risk. Exact affinity multiplicativity gives the
`shots`-th power, including zero-affinity endpoints. The generic repetition
representation bridge also identifies this same operational optimum with the
recursive `iidPower` total variation and transports every recursive decision
risk exactly to the finite-suite carrier.

No new concentration inequality, classifier, repetition encoding, or Bayes-risk
primitive is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenRobustFiniteShot

open D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
open D5.S3.Quantum.WeylChronology.GoldenRobustAffinity
open D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
open D5.S3.Estimation.ErrorExponents.FiniteSuiteAffinityProductBound
open D5.S3.Estimation.ErrorExponents.FiniteRepetitionRepresentationEquiv
open D5.S3.RenyiDivergence
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Bhattacharyya

noncomputable section

/-- Operational equal-prior Bayes error for repeated robust chronology readout
in the repository's canonical finite-suite representation. -/
def robustRepeatedOptimalError
    (leftCal rightCal : RamseyCalibration)
    (left right : List Bool) (shots : ℕ) : ℝ :=
  finiteSuiteOptimalError
    (Index := Fin shots)
    (fun _ => robustChronologyLaw leftCal left)
    (fun _ => robustChronologyLaw rightCal right)

/-- The operational robust optimum is exactly half of one minus total variation
of the recursive iidPower laws. This removes the former representation split
between recursive arbitrary-test bounds and the finite-suite optimum. -/
theorem robust_repeated_optimal_error_eq_iidPower_tv
    (leftCal rightCal : RamseyCalibration)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (shots : ℕ) :
    robustRepeatedOptimalError leftCal rightCal left right shots =
      (1 - totalVariation
        (iidPower (robustChronologyLaw leftCal left) shots)
        (iidPower (robustChronologyLaw rightCal right) shots)) / 2 := by
  have hp := robust_chronology_probability_data leftCal left hleft0 hleft1
  have hq := robust_chronology_probability_data rightCal right hright0 hright1
  unfold robustRepeatedOptimalError
  exact finite_suite_optimal_error_eq_iidPower_tv
    (robustChronologyLaw leftCal left)
    (robustChronologyLaw rightCal right)
    shots hp.2 hq.2

/-- Every recursive iid decision event has risk at least the same operational
robust optimum. The statement needs no probability hypotheses because it is a
pure finite minimum plus exact reindexing statement. -/
theorem robust_repeated_optimal_error_le_iid_decision
    (leftCal rightCal : RamseyCalibration)
    (left right : List Bool) (shots : ℕ)
    (decision : Finset (IidSpace Bool shots)) :
    robustRepeatedOptimalError leftCal rightCal left right shots ≤
      equalPriorError
        (iidPower (robustChronologyLaw leftCal left) shots)
        (iidPower (robustChronologyLaw rightCal right) shots)
        decision := by
  unfold robustRepeatedOptimalError
  exact finite_suite_optimal_error_le_iid_decision
    (robustChronologyLaw leftCal left)
    (robustChronologyLaw rightCal right)
    shots decision

/-- Repeating one robust pair independently raises its one-shot affinity to the
shot count. The operational optimum is bounded by half of that exact power. -/
theorem robust_repeated_optimal_error_le_bhattacharyya_power
    (leftCal rightCal : RamseyCalibration)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (shots : ℕ) :
    robustRepeatedOptimalError leftCal rightCal left right shots ≤
      bhattacharyya
        (robustChronologyLaw leftCal left)
        (robustChronologyLaw rightCal right) ^ shots / 2 := by
  let p : Fin shots → Bool → ℝ :=
    fun _ => robustChronologyLaw leftCal left
  let q : Fin shots → Bool → ℝ :=
    fun _ => robustChronologyLaw rightCal right
  have hp := robust_chronology_probability_data leftCal left hleft0 hleft1
  have hq := robust_chronology_probability_data rightCal right hright0 hright1
  have hbound := finite_suite_optimal_error_le_bhattacharyya_product
    p q (fun _ => hp) (fun _ => hq)
  have hproduct :
      (∏ i : Fin shots, bhattacharyya (p i) (q i)) =
        bhattacharyya
          (robustChronologyLaw leftCal left)
          (robustChronologyLaw rightCal right) ^ shots := by
    simp_rw [show ∀ i : Fin shots,
      bhattacharyya (p i) (q i) =
        bhattacharyya
          (robustChronologyLaw leftCal left)
          (robustChronologyLaw rightCal right) by
        intro i
        rfl]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hproduct] at hbound
  simpa [robustRepeatedOptimalError, p, q] using hbound

/-- Headline robust finite-shot theorem. A nonnegative certified calibration
margin gives an explicit operational Bayes-risk ceiling after `shots`
independent readouts. -/
theorem robust_repeated_optimal_error_le_margin_power
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 ≤ robustSeparationMargin leftCal rightCal v0 k0 left right)
    (shots : ℕ) :
    robustRepeatedOptimalError leftCal rightCal left right shots ≤
      Real.sqrt
          (1 - robustSeparationMargin leftCal rightCal v0 k0 left right ^ 2) ^ shots / 2 := by
  have hAffinity := robust_bhattacharyya_le_margin_ceiling
    leftCal rightCal v0 k0 left right
    hleft0 hleft1 hright0 hright1 hmargin
  have hAffinityNonnegative :
      0 ≤ bhattacharyya
        (robustChronologyLaw leftCal left)
        (robustChronologyLaw rightCal right) := by
    rw [bhattacharyya]
    exact Finset.sum_nonneg fun b _ => Real.sqrt_nonneg _
  have hPower :
      bhattacharyya
          (robustChronologyLaw leftCal left)
          (robustChronologyLaw rightCal right) ^ shots ≤
        Real.sqrt
          (1 - robustSeparationMargin leftCal rightCal v0 k0 left right ^ 2) ^ shots :=
    pow_le_pow_left₀ hAffinityNonnegative hAffinity shots
  have hOptimal := robust_repeated_optimal_error_le_bhattacharyya_power
    leftCal rightCal left right hleft0 hleft1 hright0 hright1 shots
  nlinarith

/-- A target equal-prior risk is certified whenever the robust affinity ceiling
to the shot count is at most twice that target. -/
theorem robust_repeated_target_error_of_margin_power
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hleft0 : 0 ≤ robustChronologyFringe leftCal left)
    (hleft1 : robustChronologyFringe leftCal left ≤ 1)
    (hright0 : 0 ≤ robustChronologyFringe rightCal right)
    (hright1 : robustChronologyFringe rightCal right ≤ 1)
    (hmargin : 0 ≤ robustSeparationMargin leftCal rightCal v0 k0 left right)
    (shots : ℕ) (eps : ℝ)
    (hpower :
      Real.sqrt
          (1 - robustSeparationMargin leftCal rightCal v0 k0 left right ^ 2) ^ shots ≤
        2 * eps) :
    robustRepeatedOptimalError leftCal rightCal left right shots ≤ eps := by
  have hupper := robust_repeated_optimal_error_le_margin_power
    leftCal rightCal v0 k0 left right
    hleft0 hleft1 hright0 hright1 hmargin shots
  nlinarith

#print axioms robust_repeated_optimal_error_eq_iidPower_tv
#print axioms robust_repeated_optimal_error_le_iid_decision
#print axioms robust_repeated_optimal_error_le_bhattacharyya_power
#print axioms robust_repeated_optimal_error_le_margin_power
#print axioms robust_repeated_target_error_of_margin_power

end
end D5.S3.Quantum.WeylChronology.GoldenRobustFiniteShot
