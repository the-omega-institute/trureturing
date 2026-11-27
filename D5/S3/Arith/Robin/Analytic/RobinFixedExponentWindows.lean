/- GID: D5/S3/Arith/Robin/Analytic/RobinFixedExponentWindows
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/RobinFixedExponentWindows
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Cofinal one-sided arithmetic bounds control both signed tail masses at the original exponent with logarithmic saving. -/

import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.SignedCompleteWindowExponent
import D5.S3.Weil.Mertens.WeightedTailWindowMass

/-! A fixed cofinal arithmetic power estimate controls the endpoint defect
and hence the discrepancy of the two signed window masses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U psiErrorKernel)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (Jpsi weighted_eq)
open D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope (actual_terminal_defect_exp_bound)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_re_le_abscissa)
open D5.S3.Weil.Mertens.IntegratedExplicit.SignedCompleteWindowExponent
  (zeroAbscissa_le_iff_frequently_window_bound)
open D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail transport)
open D5.S3.Weil.Mertens.WeightedTailInverse (a a_pos)
open D5.S3.Weil.Mertens.WeightedTailWindowMass (endpointDefect)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows

private lemma log_ge_one {x : ℝ} (hx : exp 1 ≤ x) : 1 ≤ log x := by
  simpa only [log_exp] using log_le_log (exp_pos 1) hx

private lemma one_lt_of_exp_one_le {x : ℝ} (hx : exp 1 ≤ x) : 1 < x :=
  (one_lt_exp_iff.mpr zero_lt_one).trans_le hx

private lemma terminal_bound {κ b : ℝ} (hκ : 0 < κ) (hhalf : κ < 1 / 2)
    (hb : 1 < b)
    (hwindows : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∃ᶠ Y : ℝ in atTop, ∀ x ∈ Icc Y (Y ^ b), U x ≤ C₀ * x ^ (1 / 2 + κ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, exp 1 ≤ x →
      |endpointDefect psiErrorKernel x| ≤ K * x ^ (κ - 1 / 2) / log x := by
  have habs : zeroAbscissa ≤ 1 / 2 + κ :=
    (zeroAbscissa_le_iff_frequently_window_bound (e := 1)
      (by linarith : (1 / 2 : ℝ) ≤ 1 / 2 + κ) hb (Or.inl rfl)).mpr
      (by simpa only [one_mul] using hwindows)
  have hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - (1 / 2 - κ) := by
    intro rho hrho
    have h := (zero_re_le_abscissa hrho).trans habs
    linarith only [h]
  obtain ⟨K, hK, hE⟩ := actual_terminal_defect_exp_bound
    (sub_pos.mpr hhalf) (by linarith : 1 / 2 - κ ≤ 1 / 2) hstrip
  refine ⟨K, hK, ?_⟩
  intro x hx
  have hx0 : 0 < x := (exp_pos 1).trans_le hx
  have htail : weightedTail psiErrorKernel x = Jpsi x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact weighted_eq t
  have h := hE (log x) (log_ge_one hx)
  rw [exp_log hx0, show -(1 / 2 - κ) = κ - 1 / 2 by ring,
    mul_comm (κ - 1 / 2) (log x), ← rpow_def_of_pos hx0] at h
  change |Q x - a x * weightedTail psiErrorKernel x| ≤ _
  rw [htail]
  exact h

/-- Scaling the positive part by the inverse weight preserves its
one-Lipschitz comparison with the signed complete tail. -/
private lemma density_discrepancy {t e : ℝ} (ht : 1 < t) (he : e = 1 ∨ e = -1) :
    |(a t / sqrt t) * max (e * (-weightedTail psiErrorKernel t)) 0 -
      max (e * (-Q t)) 0 / sqrt t| ≤ |endpointDefect psiErrorKernel t| / sqrt t := by
  have ha : 0 ≤ a t := (a_pos ht).le
  have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  have hscale : (a t / sqrt t) * max (e * (-weightedTail psiErrorKernel t)) 0 =
      max (e * (-(a t * weightedTail psiErrorKernel t))) 0 / sqrt t := by
    calc
      _ = (a t * max (e * (-weightedTail psiErrorKernel t)) 0) / sqrt t := by ring
      _ = _ := by
        rw [mul_max_of_nonneg _ _ ha, mul_zero]
        congr 2
        ring
  rw [hscale, ← sub_div, abs_div, abs_of_nonneg (sqrt_nonneg t)]
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg t)
  calc
    _ ≤ |e * (-(a t * weightedTail psiErrorKernel t)) - e * (-Q t)| :=
      abs_max_sub_max_le_abs _ _ _
    _ = |e * endpointDefect psiErrorKernel t| := by
      congr 1
      change _ = e * (Q t - a t * weightedTail psiErrorKernel t)
      ring
    _ = _ := by rw [abs_mul, heabs, one_mul]

/-- A single fixed-exponent cofinal upper estimate for the actual Mangoldt
ramp gives a terminal defect estimate and a two-sided signed mass comparison
on every later finite interval, with the same exponent and a log saving. -/
theorem signed_mass_comparison_of_frequently_window_bound {κ b : ℝ}
    (hκ : 0 < κ) (hhalf : κ < 1 / 2) (hb : 1 < b)
    :
    let observe := tail
    let q := observe psiErrorKernel
    (∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ᶠ Y : ℝ in atTop,
      ∀ x ∈ Icc Y (Y ^ b), -x * q x ≤ C₀ * x ^ (1 / 2 + κ)) →
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ x : ℝ, exp 1 ≤ x →
        |q x - a x * weightedTail psiErrorKernel x| ≤ K * x ^ (κ - 1 / 2) / log x) ∧
      (∀ A B e : ℝ, exp 1 ≤ A → A ≤ B → (e = 1 ∨ e = -1) →
        |(∫ t in A..B, (a t / sqrt t) * max (e * (-weightedTail psiErrorKernel t)) 0) -
          (∫ t in A..B, max (e * (-q t)) 0 / sqrt t)| ≤
          (K / (κ * log A)) * (B ^ κ - A ^ κ)) := by
  intro observe q hw
  have hwindows : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∃ᶠ Y : ℝ in atTop, ∀ x ∈ Icc Y (Y ^ b), U x ≤ C₀ * x ^ (1 / 2 + κ) := by
    obtain ⟨C₀, hC₀, hwin⟩ := hw
    refine ⟨C₀, hC₀, (hwin.and_eventually (eventually_ge_atTop (2 : ℝ))).mono ?_⟩
    rintro Y ⟨hY, hY2⟩ x hx
    have h := hY x hx
    change -x * Q x ≤ _ at h
    have hx2 := hY2.trans hx.1
    have hx0 : 0 < x := by linarith
    have hidentity := (div_eq_iff hx0.ne').mp
      (D5.S3.Weil.Mertens.ZeroAbscissaPower.primitive_eq_negative_tail hx2)
    rw [hidentity]
    simpa only [neg_mul, mul_neg, mul_comm] using h
  obtain ⟨K, hK, hE⟩ := terminal_bound hκ hhalf hb hwindows
  refine ⟨K, hK, hE, ?_⟩
  intro A B e hA hAB he
  have hA1 := one_lt_of_exp_one_le hA
  have hA0 := zero_lt_one.trans hA1
  have hA2 : 2 ≤ A := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h.trans hA
  have hlogA : 0 < log A := log_pos hA1
  have hk : IntegrableOn psiErrorKernel (Ioi A) :=
    chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi hA1.le)
  have hQ : ContinuousOn Q (Icc A B) :=
    hk.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)
  have hJ : ContinuousOn (weightedTail psiErrorKernel) (Icc A B) :=
    (transport hA2 hk).1.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)
  have ha : ContinuousOn a (Icc A B) := by
    intro t ht
    have ht1 := hA1.trans_le ht.1
    have hl := log_pos ht1
    have hc := continuousAt_log (zero_lt_one.trans ht1).ne'
    exact ((hc.pow 2).div (hc.const_add 1) (by positivity)).continuousWithinAt
  have hs : ∀ t ∈ Icc A B, sqrt t ≠ 0 :=
    fun t ht => (sqrt_pos.2 (hA0.trans_le ht.1)).ne'
  let f (t : ℝ) := (a t / sqrt t) * max (e * (-weightedTail psiErrorKernel t)) 0
  let g (t : ℝ) := max (e * (-Q t)) 0 / sqrt t
  have hf : IntervalIntegrable f volume A B :=
    ((ha.div continuous_sqrt.continuousOn hs).mul
      ((continuousOn_const.mul hJ.neg).sup continuousOn_const)).intervalIntegrable_of_Icc hAB
  have hg : IntervalIntegrable g volume A B :=
    (((continuousOn_const.mul hQ.neg).sup continuousOn_const).div
      continuous_sqrt.continuousOn hs).intervalIntegrable_of_Icc hAB
  have hmajor : IntervalIntegrable (fun t : ℝ => (K / log A) * t ^ (κ - 1)) volume A B :=
    (continuousOn_const.mul (continuousOn_id.rpow_const
      (fun t ht => Or.inl (hA0.trans_le ht.1).ne'))).intervalIntegrable_of_Icc hAB
  have hpoint : ∀ t ∈ Icc A B, |f t - g t| ≤ (K / log A) * t ^ (κ - 1) := by
    intro t ht
    have ht0 := hA0.trans_le ht.1
    have ht1 := hA1.trans_le ht.1
    have hpow : t ^ (κ - 1 / 2) / sqrt t = t ^ (κ - 1) := by
      rw [sqrt_eq_rpow, ← rpow_sub ht0]
      congr 1 <;> ring
    calc
      _ ≤ |endpointDefect psiErrorKernel t| / sqrt t := density_discrepancy ht1 he
      _ ≤ (K * t ^ (κ - 1 / 2) / log t) / sqrt t :=
        div_le_div_of_nonneg_right (hE t (hA.trans ht.1)) (sqrt_nonneg t)
      _ ≤ (K * t ^ (κ - 1 / 2) / log A) / sqrt t :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (mul_nonneg hK (rpow_nonneg ht0.le _))
            hlogA (log_le_log hA0 ht.1)) (sqrt_nonneg t)
      _ = _ := by
        rw [show (K * t ^ (κ - 1 / 2) / log A) / sqrt t =
          (K / log A) * (t ^ (κ - 1 / 2) / sqrt t) by ring, hpow]
  change |(∫ t in A..B, f t) - (∫ t in A..B, g t)| ≤ _
  rw [← intervalIntegral.integral_sub hf hg]
  calc
    _ ≤ ∫ t in A..B, |f t - g t| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun t => f t - g t) hAB)
    _ ≤ ∫ t in A..B, (K / log A) * t ^ (κ - 1) :=
      intervalIntegral.integral_mono_on hAB (hf.sub hg).abs hmajor hpoint
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : -1 < κ - 1)),
        sub_add_cancel]
      field_simp [hκ.ne', hlogA.ne'] <;> ring

#print axioms signed_mass_comparison_of_frequently_window_bound

end D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows
