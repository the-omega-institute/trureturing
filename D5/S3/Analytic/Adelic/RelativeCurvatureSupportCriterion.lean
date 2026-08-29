/- GID: D5/S3/Analytic/Adelic/RelativeCurvatureSupportCriterion
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/RelativeCurvatureSupportCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relative curvature support is critical exactly when all nontrivial zeta zeros are. -/

import D5.S3.Weil.ZetaRvm.CountByIntegral
import D5.S3.Zeros.CompletedZeta
import Mathlib.MeasureTheory.Measure.Support

/- Library-search audit trail (2026-08-29):
   * Repository searches for curvature support, zero-divisor support, and a
     Riemann critical-line support criterion found no exact D5 owner.
   * Frozen `IsNontrivialZero`, `zeroMult`, `one_le_mult_holds`, and the
     differentiability of `xiReading` supply the canonical zero carrier,
     positive multiplicities, and closed zero locus. The existing
     `zeroCountingMeasure` is instead a real-ordinate measure parameterized by
     an external enumeration, so it is not the source carrier here.
   * Pinned Mathlib supplies `Measure.le_sum`, `sum_apply_eq_zero'`,
     `support_eq_forall_isOpen`, and `notMem_support_iff_exists`, but no support
     theorem for an arbitrary positive weighted Dirac sum. That bridge is
     proved locally below. No new definition or alternate carrier is added. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.RelativeCurvatureSupportCriterion

open Complex MeasureTheory Set
open scoped ENNReal
open D5.S3.Zeros.CompletedZeta

private theorem xi_zero_iff_nontrivial (point : ℂ) :
    xiReading point = 0 ↔ Zeta23.IsNontrivialZero point := by
  constructor
  · intro hXi
    have hZero : point ≠ 0 := by
      intro hPoint
      subst point
      norm_num [xiReading] at hXi
    have hOne : point ≠ 1 := by
      intro hPoint
      subst point
      norm_num [xiReading] at hXi
    have hCompleted : completedRiemannZeta point = 0 := by
      rw [xi_reading_eq_completed_zeta hZero hOne] at hXi
      simpa [completedZetaReading, hZero, sub_ne_zero.mpr hOne] using hXi
    exact Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mp hCompleted
  · intro hZero
    have hPointZero : point ≠ 0 := by
      intro hPoint
      subst point
      norm_num [Zeta23.IsNontrivialZero] at hZero
    have hPointOne : point ≠ 1 := by
      intro hPoint
      subst point
      norm_num [Zeta23.IsNontrivialZero] at hZero
    rw [xi_reading_eq_completed_zeta hPointZero hPointOne]
    rw [completedZetaReading,
      Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mpr hZero]
    simp

private theorem support_weighted_dirac_sum (carrier : Set ℂ)
    (hCarrierClosed : IsClosed carrier) (weight : carrier -> ℝ≥0∞)
    (hWeightPositive : ∀ point, 0 < weight point) :
    (Measure.sum fun point : carrier =>
      weight point • Measure.dirac (point : ℂ)).support = carrier := by
  ext point
  constructor
  · intro hSupport
    by_contra hPoint
    have hComplementZero :
        Measure.sum (fun zero : carrier =>
          weight zero • Measure.dirac (zero : ℂ)) carrierᶜ = 0 := by
      apply (Measure.sum_apply_eq_zero'
        hCarrierClosed.isOpen_compl.measurableSet).2
      intro zero
      simp [Measure.smul_apply, Measure.dirac_apply, zero.property]
    have hNotSupport : point ∉
        (Measure.sum fun zero : carrier =>
          weight zero • Measure.dirac (zero : ℂ)).support :=
      Measure.notMem_support_iff_exists.mpr
        ⟨carrierᶜ, hCarrierClosed.isOpen_compl.mem_nhds hPoint,
          hComplementZero⟩
    exact hNotSupport hSupport
  · intro hPoint
    rw [Measure.support_eq_forall_isOpen]
    intro neighborhood hPointNeighborhood hNeighborhoodOpen
    let indexedPoint : carrier := ⟨point, hPoint⟩
    have hIndexedPointNeighborhood :
        (indexedPoint : ℂ) ∈ neighborhood := hPointNeighborhood
    have hWeightLe : weight indexedPoint ≤
        Measure.sum (fun zero : carrier =>
          weight zero • Measure.dirac (zero : ℂ)) neighborhood := by
      calc
        weight indexedPoint =
            (weight indexedPoint • Measure.dirac (indexedPoint : ℂ))
              neighborhood := by
          rw [Measure.smul_apply,
            Measure.dirac_apply_of_mem hIndexedPointNeighborhood]
          simp
        _ ≤ Measure.sum (fun zero : carrier =>
            weight zero • Measure.dirac (zero : ℂ)) neighborhood :=
          (Measure.le_sum (fun zero : carrier =>
            weight zero • Measure.dirac (zero : ℂ)) indexedPoint) neighborhood
    exact (hWeightPositive indexedPoint).trans_le hWeightLe

/-- The multiplicity-weighted relative-curvature measure of the canonical
nontrivial zeta zeros is supported in the critical strip. Its support inside
that strip lies on the midline exactly when every nontrivial zero does. -/
theorem relative_curvature_support_criterion :
    let zeros : Set ℂ := {point | Zeta23.IsNontrivialZero point}
    let relativeCurvature : Measure ℂ :=
      Measure.sum fun zero : zeros =>
        (Zeta23.zeroMult zero : ℝ≥0∞) • Measure.dirac (zero : ℂ)
    let criticalStrip : Set ℂ :=
      {point | 0 < point.re ∧ point.re < 1}
    let criticalLine : Set ℂ :=
      {point | point.re = (1 : ℝ) / 2}
    (∀ point, Zeta23.IsNontrivialZero point -> point ∈ criticalLine) ↔
      relativeCurvature.support ∩ criticalStrip ⊆ criticalLine := by
  classical
  dsimp only
  let zeros : Set ℂ := {point | Zeta23.IsNontrivialZero point}
  have hZerosXi : zeros = {point | xiReading point = 0} := by
    ext point
    exact (xi_zero_iff_nontrivial point).symm
  have hZerosClosed : IsClosed zeros := by
    rw [hZerosXi]
    exact isClosed_eq xi_reading_differentiable.continuous continuous_const
  have hMultiplicityPositive (zero : zeros) :
      0 < (Zeta23.zeroMult zero : ℝ≥0∞) := by
    exact_mod_cast Zeta23.ZetaSeam.one_le_mult_holds zero zero.property
  have hCurvatureSupport :
      (Measure.sum fun zero : zeros =>
        (Zeta23.zeroMult zero : ℝ≥0∞) •
          Measure.dirac (zero : ℂ)).support = zeros :=
    support_weighted_dirac_sum zeros hZerosClosed
      (fun zero => (Zeta23.zeroMult zero : ℝ≥0∞))
      hMultiplicityPositive
  change (∀ point, Zeta23.IsNontrivialZero point ->
      point.re = (1 : ℝ) / 2) ↔
    (Measure.sum fun zero : zeros =>
      (Zeta23.zeroMult zero : ℝ≥0∞) •
        Measure.dirac (zero : ℂ)).support ∩
      {point : ℂ | 0 < point.re ∧ point.re < 1} ⊆
        {point : ℂ | point.re = (1 : ℝ) / 2}
  rw [hCurvatureSupport]
  constructor
  · intro hCritical point hPoint
    exact hCritical point hPoint.1
  · intro hSupport point hZero
    exact hSupport ⟨hZero, hZero.2⟩

#print axioms relative_curvature_support_criterion

end D5.S3.Analytic.Adelic.RelativeCurvatureSupportCriterion
