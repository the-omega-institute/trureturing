/- GID: D5/S3/Arith/Robin/ForwardKernel/AveragingRegularity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/AveragingRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Double forward averages have a continuous first derivative. -/

import D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Regularity of one and two forward averages. -/

namespace D5.S3.Arith.Robin.ForwardKernel.AveragingRegularity

open Set MeasureTheory
open VarianceTransferDefs VarianceTransfer CrossExponentDefs

noncomputable section

/-- Local boundedness and measurability give integrability on finite intervals. -/
lemma locallyBoundedMeasurable_intervalIntegrable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (a b : ℝ) : IntervalIntegrable E volume a b := by
  have h := (increment_comp_integrableOn hE (K := uIcc a b)
    isCompact_uIcc continuous_id (continuous_const (y := (0 : ℝ)))).add
    (integrableOn_const (μ := volume) (C := E 0) isCompact_uIcc.measure_lt_top.ne)
  convert h.intervalIntegrable using 1
  ext y
  simp [increment]

private lemma average_primitive {E : ℝ → ℝ}
    (hi : ∀ a b, IntervalIntegrable E volume a b) (R x : ℝ) :
    windowAverage R E x =
      ((∫ y in (0 : ℝ)..(x + R), E y) - ∫ y in (0 : ℝ)..x, E y) / R := by
  unfold windowAverage
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero]
  rw [intervalIntegral.integral_interval_sub_left (hi 0 (x + R)) (hi 0 x)]

/-- A forward average is continuous whenever the averaged function is interval integrable. -/
theorem windowAverage_continuous_of_intervalIntegrable {E : ℝ → ℝ}
    (hi : ∀ a b, IntervalIntegrable E volume a b) (R : ℝ) :
    Continuous (windowAverage R E) := by
  have hp := intervalIntegral.continuous_primitive hi 0
  have he : windowAverage R E = fun x =>
      ((∫ y in (0 : ℝ)..(x + R), E y) - ∫ y in (0 : ℝ)..x, E y) / R :=
    funext (average_primitive hi R)
  rw [he]
  exact ((hp.comp (continuous_id.add continuous_const)).sub hp).div_const R

/-- A forward average of a locally bounded measurable function is continuous. -/
theorem windowAverage_continuous {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R : ℝ} (_hR : 0 < R) : Continuous (windowAverage R E) := by
  exact windowAverage_continuous_of_intervalIntegrable
    (locallyBoundedMeasurable_intervalIntegrable hE) R

private lemma average_increment {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (R x : ℝ) :
    windowAverage R (increment E R) x =
      windowAverage R E (x + R) - windowAverage R E x := by
  have hi (c : ℝ) : IntervalIntegrable (fun r => E (c + r)) volume 0 R := by
    simpa using (locallyBoundedMeasurable_intervalIntegrable hE c (c + R)).comp_add_left c
  unfold windowAverage increment
  rw [intervalIntegral.integral_sub (by simpa [add_assoc, add_comm R] using hi (x + R)) (hi x)]
  simp_rw [show ∀ r : ℝ, x + r + R = x + R + r by intro r; ring]
  ring

/-- A double average has derivative equal to the averaged increment divided by the scale. -/
theorem doubleAverage_hasDerivAt {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    HasDerivAt (doubleAverage R E)
      (windowAverage R (increment E R) x / R) x := by
  have hc := windowAverage_continuous hE hR
  have hd := (((hc.integral_hasStrictDerivAt 0 (x + R)).hasDerivAt.comp x
    ((hasDerivAt_id x).add_const R)).sub
      (hc.integral_hasStrictDerivAt 0 x).hasDerivAt).div_const R
  have he : doubleAverage R E = fun x =>
      ((∫ y in (0 : ℝ)..(x + R), windowAverage R E y) -
        ∫ y in (0 : ℝ)..x, windowAverage R E y) / R :=
    funext (average_primitive (fun a b => hc.intervalIntegrable a b) R)
  rw [he, average_increment hE]
  simpa using hd

/-- A double forward average has a continuous first derivative. -/
theorem doubleAverage_contDiff {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R : ℝ} (hR : 0 < R) : ContDiff ℝ 1 (doubleAverage R E) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (doubleAverage_hasDerivAt hE hR x).differentiableAt, ?_⟩
  have he : deriv (doubleAverage R E) = fun x =>
      (windowAverage R E (x + R) - windowAverage R E x) / R := by
    funext x
    rw [(doubleAverage_hasDerivAt hE hR x).deriv, average_increment hE]
  rw [he]
  have hc := windowAverage_continuous hE hR
  exact ((hc.comp (continuous_id.add continuous_const)).sub hc).div_const R

end
end D5.S3.Arith.Robin.ForwardKernel.AveragingRegularity
