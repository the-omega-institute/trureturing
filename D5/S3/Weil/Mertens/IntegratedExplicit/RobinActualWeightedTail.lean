/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedTail
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedTail
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: The weighted transport of the actual zero series is the sum of its occurrence responses. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U psiErrorKernel)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace

private lemma mode_norm_bound {c z : ℂ} (hz : z.re < 1) {v : ℝ} (hv : 0 ≤ v) :
    ‖integratedZeroMode c z v‖ ≤ ‖c‖ := by
  rw [integratedZeroMode, norm_mul, norm_neg, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.sub_re, Complex.one_re]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv))

private lemma mode_d_integrable {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) {c z : ℂ}
    (hz : z.re < 1) : IntegrableOn (fun v => (d j v : ℂ) * integratedZeroMode c z v) (Ioi u) := by
  apply ((d_integrable hj hu).mul_const ‖c‖).mono'
  · exact (show ContinuousOn (fun v => (d j v : ℂ) * integratedZeroMode c z v) (Ioi u) by
      intro v hv
      have hv0 := hu.trans hv
      unfold d H integratedZeroMode
      fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d_nonneg hj (hu.trans hv))]
    exact mul_le_mul_of_nonneg_left (mode_norm_bound hz (hu.trans hv).le) (d_nonneg hj (hu.trans hv))

private lemma mode_A_deriv_integrable {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) {c z : ℂ}
    (hz : z.re < 1) : IntegrableOn (fun v => (A j v : ℂ) *
      (c * (1-z) * Complex.exp ((z-1)*(v:ℂ)))) (Ioi u) := by
  apply ((integrableOn_exp_mul_Ioi (show z.re-j < 0 by linarith) u).const_mul
    (H j u * ‖c * (1-z)‖)).mono'
  · exact (show ContinuousOn (fun v => (A j v : ℂ) *
        (c * (1-z) * Complex.exp ((z-1)*(v:ℂ)))) (Ioi u) by
      intro v hv
      have hv0 := hu.trans hv
      unfold A H
      fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (A_nonneg hj (hu.trans hv)), Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, Complex.one_re]
    change A j v * (‖c * (1-z)‖ * Real.exp ((z.re-1)*v)) ≤ _
    unfold A
    have he : Real.exp ((1-j)*v) * Real.exp ((z.re-1)*v) = Real.exp ((z.re-j)*v) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show Real.exp ((1-j)*v) * H j v * (‖c*(1-z)‖ * Real.exp ((z.re-1)*v)) =
      H j v * ‖c*(1-z)‖ * (Real.exp ((1-j)*v) * Real.exp ((z.re-1)*v)) by ring, he]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (H_antitone (by linarith) hu hv.le) (norm_nonneg _)) (Real.exp_nonneg _)

/-- Integration by parts for an individual mode, with both endpoints accounted for. -/
theorem mode_transport_eq {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) {c z : ℂ} (hz : z.re < 1) :
    (A j u : ℂ) * integratedZeroMode c z u -
      (∫ v in Ioi u, (d j v : ℂ) * integratedZeroMode c z v) =
      weightedZeroContribution j c z u := by
  let f : ℝ → ℂ := fun v => (A j v : ℂ)
  let g : ℝ → ℂ := integratedZeroMode c z
  let f' : ℝ → ℂ := fun v => -(d j v : ℂ)
  let g' : ℝ → ℂ := fun v => c*(1-z)*Complex.exp ((z-1)*(v:ℂ))
  have hf {v : ℝ} (hv : 0 < v) : HasDerivAt f (f' v) v := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt v (A_hasDerivAt j hv)
    simpa [f,f',Function.comp_def] using h
  have hg (v : ℝ) : HasDerivAt g (g' v) v := integratedZeroMode_hasDerivAt c z v
  have hi : IntegrableOn (f * g') (Ioi u) := mode_A_deriv_integrable hj hu hz
  have hd : IntegrableOn (f' * g) (Ioi u) := by
    have h := (mode_d_integrable (c:=c) (z:=z) hj hu hz).neg
    simpa [f',g,Pi.mul_def,neg_mul] using h
  have hend : Tendsto (f * g) (𝓝[>] u) (𝓝 (f u * g u)) :=
    (((hf hu).continuousAt.mul (hg u).continuousAt).continuousWithinAt)
  have hinfty : Tendsto (f * g) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun v => A j v * ‖c‖) ?_ (by simpa using (A_tendsto_zero hj).mul_const ‖c‖)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
    change ‖(A j v : ℂ) * integratedZeroMode c z v‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (A_nonneg hj hv)]
    exact mul_le_mul_of_nonneg_left (mode_norm_bound hz hv.le) (A_nonneg hj hv)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (fun v hv => hf (hu.trans hv))
    (fun v _ => hg v) hi hd hend hinfty
  change (∫ v in Ioi u, f v * g' v) = 0 - f u * g u - ∫ v in Ioi u, f' v * g v at h
  have hneg : weightedZeroContribution j c z u = -(∫ v in Ioi u, f v * g' v) := by
    rw [weightedZeroContribution_eq_integral_deriv, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    change -(Real.exp ((1-j)*v):ℂ) * (H j v:ℂ) * deriv (integratedZeroMode c z) v = -(f v * g' v)
    rw [(integratedZeroMode_hasDerivAt c z v).deriv]
    simp [f,g',A]
  rw [hneg,h]
  dsimp [f,g,f']
  simp_rw [neg_mul, integral_neg]
  ring

def zeroQ (v : ℝ) : ℂ := -((Real.exp (-v):ℝ):ℂ) * actualH v

private lemma zeroQ_hasSum (v : ℝ) : HasSum
    (fun k => integratedZeroMode (actualCoeff k) (actualZero k) v) (zeroQ v) := by
  have h := (actualH_summable v).hasSum.mul_left (-((Real.exp (-v):ℝ):ℂ))
  change HasSum _ (zeroQ v) at h
  convert h using 1
  funext k
  unfold integratedZeroMode
  rw [Complex.ofReal_exp, show (↑(-v):ℂ) = -(v:ℂ) by push_cast; rfl]
  rw [show -(Complex.exp (-(v:ℂ))) * (actualCoeff k * Complex.exp ((v:ℂ) * actualZero k)) =
    -actualCoeff k * (Complex.exp (-(v:ℂ)) * Complex.exp ((v:ℂ)*actualZero k)) by ring,
    ← Complex.exp_add]
  congr 2
  ring

private lemma zero_re_lt_one (k : ℕ) : (actualZero k).re < 1 :=
  (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2

lemma zeroQ_d_integrable {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) :
    IntegrableOn (fun v => (d j v : ℂ) * zeroQ v) (Ioi u) := by
  let M := ∑' k, ‖actualCoeff k‖
  apply ((d_integrable hj hu).mul_const M).mono'
  · exact (show ContinuousOn (fun v => (d j v : ℂ) * zeroQ v) (Ioi u) by
      have hc : Continuous zeroQ := by unfold zeroQ; exact (by fun_prop : Continuous (fun v : ℝ => -(↑(Real.exp (-v)):ℂ))).mul actualH_continuous
      apply ContinuousOn.mul _ hc.continuousOn
      intro v hv
      have hv0 := hu.trans hv
      unfold d H
      fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d_nonneg hj (hu.trans hv))]
    apply mul_le_mul_of_nonneg_left _ (d_nonneg hj (hu.trans hv))
    rw [← (zeroQ_hasSum v).tsum_eq]
    exact tsum_of_norm_bounded actualCoeff_hasSum.summable.norm.hasSum
      (fun k => mode_norm_bound (zero_re_lt_one k) (hu.trans hv).le)

private lemma zeroQ_d_exchange {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) : HasSum
    (fun k => ∫ v in Ioi u, (d j v : ℂ) * integratedZeroMode (actualCoeff k) (actualZero k) v)
    (∫ v in Ioi u, (d j v : ℂ) * zeroQ v) := by
  apply hasSum_integral_of_dominated_convergence (fun k v => d j v * ‖actualCoeff k‖)
  · intro k
    exact (mode_d_integrable (c:=actualCoeff k) (z:=actualZero k) hj hu (zero_re_lt_one k)).aestronglyMeasurable
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d_nonneg hj (hu.trans hv))]
    exact mul_le_mul_of_nonneg_left (mode_norm_bound (zero_re_lt_one k) (hu.trans hv).le) (d_nonneg hj (hu.trans hv))
  · exact ae_of_all _ fun _ => actualCoeff_hasSum.summable.norm.mul_left _
  · simpa only [tsum_mul_left] using (d_integrable hj hu).mul_const (∑' k, ‖actualCoeff k‖)
  · exact ae_of_all _ fun v => (zeroQ_hasSum v).mul_left _

theorem zeroQ_response {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) :
    (A j u : ℂ) * zeroQ u - (∫ v in Ioi u, (d j v : ℂ) * zeroQ v) =
      ∑' k, actualWeightedZeroContribution j k u := by
  have h := ((zeroQ_hasSum u).mul_left (A j u : ℂ)).sub (zeroQ_d_exchange hj hu)
  rw [← h.tsum_eq]
  apply tsum_congr
  intro k
  simpa only [actualWeightedZeroContribution, Pi.sub_apply] using mode_transport_eq
    (c:=actualCoeff k) (z:=actualZero k) hj hu (zero_re_lt_one k)

end D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
