/- GID: D5/S3/Analytic/Adelic/PositiveTorusCarrierCriterion
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/PositiveTorusCarrierCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive torus period with critical zeros forces zeta zeros onto the midline. -/

import D5.S3.Weil.ZetaRvm.CountByIntegral
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/- Library-search audit trail (2026-08-29):
   * Repository searches for positive torus measures, Eisenstein period
     factorization, and a period-zero criterion found no exact D5 owner.
   * Frozen `completedRiemannZeta_eq_zero_iff` is the exact bridge from the
     canonical nontrivial-zero predicate to the completed-zeta factor, and
     frozen `zeta_reflect_zero` supplies the left-to-right reflection step.
   * Pinned Mathlib supplies `Measure.sum`, the Bochner integral, and the
     elementary product-zero simplification, but no whole period criterion.
     The source measure, period, and auxiliary factor are constructed directly
     below; no new definition or alternate carrier is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.PositiveTorusCarrierCriterion

open Complex MeasureTheory Set
open scoped ENNReal

/-- A nonnegative weighted sum of torus measures defines an Eisenstein period
and its weighted twist factor. If the Hecke factorization is regular on the
open right half-plane and every nontrivial period zero is critical, then every
nontrivial Riemann-zeta zero lies on the critical line. -/
theorem positive_torus_carrier_condition {Index Torus : Type*}
    [MeasurableSpace Torus] (weights : Index -> NNReal)
    (periodMeasure : Index -> Measure Torus)
    (eisenstein : Torus -> ℂ -> ℂ)
    (localFactor twistedCompleted : Index -> ℂ -> ℂ) :
    let mu : Measure Torus := Measure.sum fun index =>
      (weights index : ℝ≥0∞) • periodMeasure index
    let period : ℂ -> ℂ := fun point => ∫ z, eisenstein z point ∂mu
    let auxiliary : ℂ -> ℂ := fun point => ∑' index,
      ((weights index : ℝ) : ℂ) * localFactor index point *
        twistedCompleted index point
    let rightHalfPlane : Set ℂ :=
      {point | (1 : ℝ) / 2 < point.re}
    (∀ point, AnalyticAt ℂ auxiliary point -> auxiliary point ≠ 0 ->
      period point = completedRiemannZeta point * auxiliary point) ->
    (∀ point, period point = 0 -> 0 < point.re -> point.re < 1 ->
      point.re = (1 : ℝ) / 2) ->
    AnalyticOnNhd ℂ auxiliary rightHalfPlane ->
    (∀ point ∈ rightHalfPlane, auxiliary point ≠ 0) ->
    ∀ rho : ℂ, Zeta23.IsNontrivialZero rho ->
      rho.re = (1 : ℝ) / 2 := by
  classical
  dsimp only
  intro factorization periodZerosCritical auxiliaryAnalytic auxiliaryNonzero rho hRho
  have rightHalfZeroCritical (point : ℂ)
      (hPoint : Zeta23.IsNontrivialZero point)
      (hRight : (1 : ℝ) / 2 < point.re) :
      point.re = (1 : ℝ) / 2 := by
    have hCompleted : completedRiemannZeta point = 0 :=
      Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mpr hPoint
    have hRightMembership : point ∈ {s : ℂ | (1 : ℝ) / 2 < s.re} := hRight
    have hAnalytic := auxiliaryAnalytic point hRightMembership
    have hNonzero := auxiliaryNonzero point hRightMembership
    have hPeriodZero :
        (∫ z, eisenstein z point ∂Measure.sum (fun index =>
          (weights index : ℝ≥0∞) • periodMeasure index)) = 0 := by
      rw [factorization point hAnalytic hNonzero, hCompleted, zero_mul]
    exact periodZerosCritical point hPeriodZero hPoint.2.1 hPoint.2.2
  by_cases hRight : (1 : ℝ) / 2 < rho.re
  · exact rightHalfZeroCritical rho hRho hRight
  by_cases hCritical : rho.re = (1 : ℝ) / 2
  · exact hCritical
  have hLeft : rho.re < (1 : ℝ) / 2 :=
    lt_of_le_of_ne (le_of_not_gt hRight) hCritical
  have hReflectedZero := Zeta23.zeta_reflect_zero rho hRho
  have hReflectedRight :
      (1 : ℝ) / 2 < (Zeta23.reflect rho).re := by
    simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re,
      Complex.conj_re]
    linarith
  have hReflectedCritical :=
    rightHalfZeroCritical (Zeta23.reflect rho) hReflectedZero hReflectedRight
  simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hReflectedCritical
  linarith

#print axioms positive_torus_carrier_condition

end D5.S3.Analytic.Adelic.PositiveTorusCarrierCriterion
