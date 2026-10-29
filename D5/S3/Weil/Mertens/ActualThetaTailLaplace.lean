/- GID: D5/S3/Weil/Mertens/ActualThetaTailLaplace
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/ActualThetaTailLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual activation-weighted theta tails in logarithmic coordinates. -/

import D5.S3.Weil.Mertens.WeightedPrimeLimit
import D5.S3.Weil.Mertens.ThetaLaplaceContinuation
import D5.S3.Arith.Robin.ActualRobinClockCovariance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The signed theta tail uses the actual reciprocal logarithmic activation density. -/

namespace D5.S3.Weil.Mertens.ActualThetaTailLaplace

open Real Set MeasureTheory Filter
open scoped Topology
open ThetaLaplaceContinuation (q Q)

noncomputable section

/-- The logarithmic lower threshold. -/
def u₀ : ℝ := Real.log 2

/-- The actual activation-weighted source in logarithmic coordinates. -/
def k (u : ℝ) : ℝ := q u * (u + 1) / u ^ 2

/-- The original signed tail in the original real variable. -/
def F (x : ℝ) : ℝ :=
  -(∫ t in Ioi x, (Chebyshev.theta t - t) *
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t)

/-- The logarithmic signed tail. -/
def f (u : ℝ) : ℝ := -(∫ v in Ioi u, k v)

/-- The actual cutoff Laplace transform of the signed tail. -/
def L (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) * (f u : ℂ)

private lemma u₀_pos : 0 < u₀ := Real.log_pos (by norm_num)

private lemma theta_kernel_integrable :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioi 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hr : IntegrableOn (fun t : ℝ => Real.sqrt t / t ^ 2) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := (1 / 2 : ℝ) - 2)
      (by norm_num) one_pos).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Real.sqrt_eq_rpow, Real.rpow_sub ht0, Real.rpow_two]
  have hm : Measurable (fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) :=
    (Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).div
      (measurable_id.pow_const 2)
  have hd : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      (Ioi 1) := by
    refine (hr.const_mul C).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)),
      abs_of_nonneg (sq_nonneg t)]
    exact (div_le_div_of_nonneg_right (hC t) (sq_nonneg t)).trans_eq (by ring)
  convert WeightedPrimeLimit.chebyshev_error_kernel_integrable.sub hd using 1
  ext t
  ring

private lemma q_integrable : IntegrableOn q (Ioi u₀) := by
  have ht := theta_kernel_integrable.mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2))
  have he := (integrableOn_comp_exp_Ioi
    (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) u₀).mpr
    (by simpa [u₀] using ht)
  refine he.congr_fun ?_ measurableSet_Ioi
  intro u _
  dsimp [q]
  rw [smul_eq_mul, Real.exp_neg]
  field_simp

private lemma q_measurable : Measurable q := by
  unfold q
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-u))).mul
    ((Chebyshev.theta_mono.measurable.comp (by fun_prop)).sub (by fun_prop))

private lemma k_measurable : Measurable k :=
  ((q_measurable.mul (measurable_id.add_const 1)).div (measurable_id.pow_const 2))

private lemma weight_bound {u : ℝ} (hu : u₀ ≤ u) :
    0 ≤ (u + 1) / u ^ 2 ∧ (u + 1) / u ^ 2 ≤ (u₀ + 1) / u₀ ^ 2 := by
  have h0 := u₀_pos
  have hu0 : 0 < u := h0.trans_le hu
  constructor
  · positivity
  · have hi : 1 / u ≤ 1 / u₀ := one_div_le_one_div_of_le h0 hu
    have hi2 : 1 / u ^ 2 ≤ 1 / u₀ ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos h0) (pow_le_pow_left₀ h0.le hu 2)
    calc
      (u + 1) / u ^ 2 = 1 / u + 1 / u ^ 2 := by field_simp; ring
      _ ≤ 1 / u₀ + 1 / u₀ ^ 2 := add_le_add hi hi2
      _ = (u₀ + 1) / u₀ ^ 2 := by field_simp; ring

private lemma k_integrable : IntegrableOn k (Ioi u₀) := by
  refine (q_integrable.norm.const_mul ((u₀ + 1) / u₀ ^ 2)).mono'
    k_measurable.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [k, div_eq_mul_inv, ← mul_assoc, norm_mul]
  have hw := weight_bound hu.le
  have hn : ‖(u + 1) * (u ^ 2)⁻¹‖ ≤ (u₀ + 1) / u₀ ^ 2 := by
    simpa only [← div_eq_mul_inv, Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (q u))]

private lemma exp_activation (u : ℝ) :
    Real.exp u * ((Chebyshev.theta (Real.exp u) - Real.exp u) *
      D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity (Real.exp u)) = k u := by
  dsimp [D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity, k, q]
  rw [Real.log_exp, Real.exp_neg]
  field_simp

private lemma original_integrable {U : ℝ} (hU : u₀ ≤ U) :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
      D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) (Ioi (Real.exp U)) := by
  apply (integrableOn_comp_exp_Ioi _ U).mp
  refine (k_integrable.mono_set (Ioi_subset_Ioi hU)).congr_fun ?_ measurableSet_Ioi
  intro u _
  exact (exp_activation u).symm

private lemma tail_substitution (u : ℝ) : f u = F (Real.exp u) := by
  unfold f F
  congr 1
  have h := integral_comp_exp_Ioi (fun t : ℝ => (Chebyshev.theta t - t) *
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) u
  simpa only [smul_eq_mul, exp_activation] using h

/-- The actual theta source is absolutely integrable at zero frequency, and the
original activation tail agrees with its logarithmic-coordinate tail. -/
theorem actual_theta_tail_source :
    IntegrableOn q (Ioi u₀) ∧ IntegrableOn k (Ioi u₀) ∧
    (∀ U : ℝ, u₀ ≤ U → IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
      D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) (Ioi (Real.exp U))) ∧
    (∀ u : ℝ, f u = F (Real.exp u)) :=
  ⟨q_integrable, k_integrable, fun _ h => original_integrable h, tail_substitution⟩

#print axioms actual_theta_tail_source

end
end D5.S3.Weil.Mertens.ActualThetaTailLaplace
