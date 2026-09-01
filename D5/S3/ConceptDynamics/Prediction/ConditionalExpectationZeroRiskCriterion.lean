/- GID: D5/S3/ConceptDynamics/Prediction/ConditionalExpectationZeroRiskCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Prediction/ConditionalExpectationZeroRiskCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero squared prediction risk exactly characterizes a.e. observation measurability. -/

import D5.S3.ConceptDynamics.Prediction.ConditionalExpectationOptimality
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/- Library-search audit trail (2026-08-26):
   * Repository searches found the adjacent conditional-expectation optimality
     and refinement Pythagoras theorems, but no zero-risk characterization.
   * Pinned Mathlib has no exact packaged iff. The proof below applies
     `integral_eq_zero_iff_of_nonneg` to the canonical squared residual and
     `condExp_of_aestronglyMeasurable'` to its measurable fixed points.
   * The observation sigma-algebra is constructed canonically as the comap of
     the source observation map; no replacement risk or sigma-algebra is defined. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Prediction.ConditionalExpectationZeroRiskCriterion

open MeasureTheory
open scoped ENNReal MeasureTheory

/-- For a square-integrable real target on a probability space, the expected
squared residual from conditional prediction on the observation-generated
sigma-algebra vanishes exactly when the target is measurable there almost
everywhere. -/
theorem zero_prediction_risk_iff_ae_observation_measurable
    {X O : Type*} [MeasurableSpace X] [MeasurableSpace O]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (observation : X -> O) (hObservation : Measurable observation)
    (target : X -> Real) (hTarget : MemLp target 2 mu) :
    (∫ x, (target x -
        MeasureTheory.condExp (MeasurableSpace.comap observation inferInstance)
          mu target x) ^ 2 ∂mu) = 0 ↔
      AEStronglyMeasurable[MeasurableSpace.comap observation inferInstance]
        target mu := by
  let projected : Lp Real 2 mu :=
    ↑(condExpL2 Real Real hObservation.comap_le (hTarget.toLp target))
  have hProjectedEq :
      (projected : X -> Real) =ᵐ[mu]
        MeasureTheory.condExp
          (MeasurableSpace.comap observation inferInstance) mu target := by
    simpa only [projected] using
      (MemLp.condExpL2_ae_eq_condExp hObservation.comap_le hTarget)
  have hResidualLp :
      MemLp
        (target - MeasureTheory.condExp
          (MeasurableSpace.comap observation inferInstance) mu target)
        2 mu :=
    hTarget.sub <| MemLp.ae_eq hProjectedEq (Lp.memLp projected)
  have hResidualIntegrable :
      Integrable
        ((target - MeasureTheory.condExp
          (MeasurableSpace.comap observation inferInstance) mu target) ^ 2)
        mu :=
    hResidualLp.integrable_sq
  rw [integral_eq_zero_iff_of_nonneg
    (fun x => sq_nonneg
      (target x -
        MeasureTheory.condExp (MeasurableSpace.comap observation inferInstance)
          mu target x))
    hResidualIntegrable]
  constructor
  · intro hZero
    have hTargetEq :
        target =ᵐ[mu]
          MeasureTheory.condExp (MeasurableSpace.comap observation inferInstance)
            mu target := by
      filter_upwards [hZero] with x hx
      change (target x -
        MeasureTheory.condExp (MeasurableSpace.comap observation inferInstance)
          mu target x) ^ 2 = 0 at hx
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
    exact stronglyMeasurable_condExp.aestronglyMeasurable.congr hTargetEq.symm
  · intro hMeasurable
    have hFixed :
        MeasureTheory.condExp (MeasurableSpace.comap observation inferInstance)
            mu target =ᵐ[mu]
          target :=
      condExp_of_aestronglyMeasurable' hObservation.comap_le hMeasurable
        (hTarget.integrable one_le_two)
    filter_upwards [hFixed] with x hx
    change (target x -
      MeasureTheory.condExp (MeasurableSpace.comap observation inferInstance)
        mu target x) ^ 2 = 0
    simp [hx]

#print axioms zero_prediction_risk_iff_ae_observation_measurable

end D5.S3.ConceptDynamics.Prediction.ConditionalExpectationZeroRiskCriterion
