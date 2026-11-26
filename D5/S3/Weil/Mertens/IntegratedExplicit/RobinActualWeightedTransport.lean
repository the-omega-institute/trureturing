/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedTransport
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedTransport
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: The logarithmic Robin weight transports integrable tails by absolute Fubini. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import D5.S3.Weil.Mertens.WeightedTailTransport

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

def A (j v : ℝ) : ℝ := Real.exp ((1-j)*v) * H j v

def d (j v : ℝ) : ℝ := Real.exp ((1-j)*v) * ((j-1)*H j v + j/v^2 + 2/v^3)

lemma A_hasDerivAt (j : ℝ) {v : ℝ} (hv : 0 < v) : HasDerivAt (A j) (-d j v) v := by
  have hv0 := hv.ne'
  have h := (((hasDerivAt_id v).const_mul (1-j)).exp.mul
    (((hasDerivAt_const v j).div (hasDerivAt_id v) hv0).add
      ((hasDerivAt_const v (1:ℝ)).div ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv0))))
  convert h using 1
  · ext; simp [A,H]
  · dsimp [d,H]; field_simp [hv0]; ring

lemma d_nonneg {j v : ℝ} (hj : 1 ≤ j) (hv : 0 < v) : 0 ≤ d j v := by
  unfold d
  have hj0 : 0 ≤ j := by linarith
  have hj1 : 0 ≤ j-1 := by linarith
  have h := H_nonneg hj0 hv
  positivity

lemma A_nonneg {j v : ℝ} (hj : 1 ≤ j) (hv : 0 < v) : 0 ≤ A j v :=
  mul_nonneg (Real.exp_nonneg _) (H_nonneg (by linarith) hv)

lemma A_tendsto_zero {j : ℝ} (hj : 1 ≤ j) : Tendsto (A j) atTop (𝓝 0) := by
  have hi : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hH : Tendsto (H j) atTop (𝓝 0) := by
    change Tendsto (fun v => H j v) atTop (𝓝 0)
    simpa [H, div_eq_mul_inv, inv_pow] using (hi.const_mul j).add (hi.pow 2)
  apply squeeze_zero_norm' (a := H j) ?_ hH
  filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (A_nonneg hj hv)]
  exact mul_le_of_le_one_left (H_nonneg (by linarith) hv)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv.le))

lemma d_integrable {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) : IntegrableOn (d j) (Ioi u) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := -A j)
  · intro v hv
    simpa only [neg_neg, Pi.neg_apply] using (A_hasDerivAt j (hu.trans_le hv)).neg
  · intro v hv
    exact d_nonneg hj (hu.trans hv)
  · change Tendsto (fun v => -A j v) atTop (𝓝 0)
    simpa using (A_tendsto_zero hj).neg

lemma d_mass {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u) : (∫ v in Ioi u, d j v) = A j u := by
  simpa only [Pi.neg_apply, zero_sub, neg_neg] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := -A j)
    (fun v hv => by simpa only [neg_neg, Pi.neg_apply] using (A_hasDerivAt j (hu.trans_le hv)).neg)
    (d_integrable hj hu) (show Tendsto (-A j) atTop (𝓝 0) by
      change Tendsto (fun v => -A j v) atTop (𝓝 0)
      simpa using (A_tendsto_zero hj).neg)

lemma d_interval {j u v : ℝ} (hj : 1 ≤ j) (hu : 0 < u) (huv : u ≤ v) :
    (∫ t in u..v, d j t) = A j u - A j v := by
  have hi : IntervalIntegrable (d j) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
    exact (d_integrable hj hu).mono_set Ioc_subset_Ioi_self
  have hd : ∀ t ∈ uIcc u v, HasDerivAt (-A j) (d j t) t := by
    intro t ht
    rw [uIcc_of_le huv] at ht
    simpa only [neg_neg, Pi.neg_apply] using (A_hasDerivAt j (hu.trans_le ht.1)).neg
  simpa only [Pi.neg_apply, neg_sub_neg] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

/-- Absolute weighted-tail transport in the logarithmic variable. -/
theorem logarithmic_transport {K : ℝ → ℝ} {j u : ℝ} (hj : 1 ≤ j) (hu : 0 < u)
    (hK : IntegrableOn K (Ioi u)) :
    IntegrableOn (fun v => K v * A j v) (Ioi u) ∧
    IntegrableOn (fun v => d j v * (∫ t in Ioi v, K t)) (Ioi u) ∧
    (∫ v in Ioi u, K v * A j v) = A j u * (∫ t in Ioi u, K t) -
      ∫ v in Ioi u, d j v * (∫ t in Ioi v, K t) := by
  let triangle (v t : ℝ) := {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => d j p.1 * K p.2) (v,t)
  have htri : Integrable (Function.uncurry triangle)
    ((volume.restrict (Ioi u)).prod (volume.restrict (Ioi u))) :=
    ((d_integrable hj hu).mul_prod hK).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hright (v : ℝ) (hv : u < v) :
      (∫ t in Ioi u, triangle v t) = d j v * (∫ t in Ioi v, K t) := by
    have heq : triangle v = (Ioi v).indicator (fun t => d j v * K t) := by ext t; rfl
    rw [heq, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hv.le), integral_const_mul]
  have hleft (t : ℝ) (ht : u < t) :
      (∫ v in Ioi u, triangle v t) = K t * (A j u - A j t) := by
    have heq : (fun v => triangle v t) = (Iio t).indicator (fun v => d j v * K t) := by ext v; rfl
    rw [heq, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Ioi_inter_Iio, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ht.le, d_interval hj hu ht.le]
    ring
  have hdelta : IntegrableOn (fun t => K t * (A j u - A j t)) (Ioi u) := by
    apply htri.integral_prod_right.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hleft t ht
  have hKA : IntegrableOn (fun t => K t * A j t) (Ioi u) := by
    apply ((hK.mul_const (A j u)).sub hdelta).congr
    filter_upwards with v
    simp only [Pi.sub_apply]
    ring
  have htail : IntegrableOn (fun v => d j v * (∫ t in Ioi v, K t)) (Ioi u) := by
    apply htri.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv using hright v hv
  have hswap := integral_integral_swap htri
  rw [setIntegral_congr_fun measurableSet_Ioi hright,
    setIntegral_congr_fun measurableSet_Ioi hleft] at hswap
  have hsplit : (∫ t in Ioi u, K t * (A j u - A j t)) =
      (∫ t in Ioi u, K t) * A j u - (∫ t in Ioi u, K t * A j t) := by
    simp_rw [mul_sub]; rw [integral_sub (hK.mul_const _) hKA, integral_mul_const]
  rw [hsplit] at hswap
  exact ⟨hKA, htail, by linarith [mul_comm (A j u) (∫ t in Ioi u, K t)]⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
