/- GID: D5/S3/Arith/Robin/Analytic/ActualUnattainedThetaWindows
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ActualUnattainedThetaWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The weighted Robin theta tail has both signs in every late fixed logarithmic window. -/

import D5.S3.Arith.Robin.Analytic.ActualUnattainedWeightedWindows
import D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich

/-! Prime powers contribute only at the square-root scale to the weighted tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.Analytic.ActualUnattainedWeightedWindows
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (Jpsi S A D tails A_data S_sub_A_limit)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open D5.S3.Weil.Mertens.ActualThetaTailLaplace (F)

namespace D5.S3.Arith.Robin.Analytic.ActualUnattainedThetaWindows

private lemma neg_F_eq_Jpsi_sub_S {x : ℝ} (hx : 2 ≤ x) : -F x = Jpsi x - S x := by
  rw [F, neg_neg, Jpsi, S, ← integral_sub (tails hx).1 (tails hx).2.1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

private lemma eventually_S_log_bound :
    ∀ᶠ t : ℝ in atTop, |S (Real.exp t)| ≤ 3 / (Real.exp (t / 2) * t) := by
  have hlimit := Real.tendsto_exp_atTop.eventually
    ((Metric.tendsto_nhds.mp S_sub_A_limit) 1 zero_lt_one)
  filter_upwards [hlimit, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  let x := Real.exp t
  have hx : 1 < x := Real.one_lt_exp_iff.mpr htpos
  have hD : 0 < D x := mul_pos (Real.sqrt_pos.mpr (Real.exp_pos t)) (Real.log_pos hx)
  have hA := (A_data hx).2.2
  change A x ≤ 2 / D x at hA
  have hAD : D x * A x ≤ 2 := by
    rw [mul_comm]
    exact (le_div_iff₀ hD).mp hA
  change dist (D x * (S x - A x)) 0 < 1 at ht
  rw [Real.dist_eq, sub_zero, mul_sub] at ht
  have hS : 0 ≤ S x := by
    unfold S
    refine setIntegral_nonneg measurableSet_Ioi (fun v hv => ?_)
    exact mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi v))
      (D5.S3.Arith.Robin.MellinWeightedVariation.weight_nonneg (hx.trans hv))
  have hDform : D x = Real.exp (t / 2) * t := by
    dsimp [D, x]
    rw [Real.log_exp, Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 2
    ring
  rw [abs_of_nonneg hS, ← hDform]
  apply (le_div_iff₀ hD).2
  have hdiff := (abs_lt.mp ht).2
  linarith only [hAD, hdiff]

/-- When the actual zero abscissa is unattained and strictly exceeds the
prescribed strip, the weighted Robin theta tail has quantitatively deep
values of both signs in every sufficiently late fixed-width logarithmic window. -/
theorem eventually_actual_weighted_theta_tail_two_signs {σ h : ℝ}
    (hσ : 1 / 2 < σ) (hσΘ : σ < zeroAbscissa) (hh : 0 < h)
    (hun : ∀ z : ℂ, D5.S3.Weil.ZeroSum.IsNontrivialZero z → z.re < zeroAbscissa) :
    ∃ β : ℝ, σ < β ∧ β < 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ T : ℝ in atTop,
        (∃ t ∈ Icc T (T + h), c * Real.exp ((β - 1) * T) / T < -F (Real.exp t)) ∧
        (∃ t ∈ Icc T (T + h), -F (Real.exp t) < -(c * Real.exp ((β - 1) * T) / T)) := by
  obtain ⟨β, hβσ, hβ₁, c, hc, hpsi⟩ :=
    eventually_actual_weighted_psi_tail_two_signs hσ hσΘ hh hun
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp eventually_S_log_bound
  have hβhalf : 1 / 2 < β := hσ.trans hβσ
  have hlimit : Tendsto (fun T : ℝ => 3 * Real.exp ((1 / 2 - β) * T)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hβhalf))
    simpa only [Function.comp_def, id_eq, mul_zero] using he.const_mul (3 : ℝ)
  refine ⟨β, hβσ, hβ₁, c / 2, half_pos hc, ?_⟩
  filter_upwards [hpsi, eventually_ge_atTop T₀, eventually_ge_atTop (Real.log 2),
    hlimit.eventually_lt_const (half_pos hc)] with T hpsiT hT hlog hsmall
  have hTpos : 0 < T := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hlog
  have hpay (t : ℝ) (ht : T ≤ t) :
      |S (Real.exp t)| ≤ (c / 2) * Real.exp ((β - 1) * T) / T := by
    have hden : Real.exp (T / 2) * T ≤ Real.exp (t / 2) * t := by
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) ht hTpos.le (Real.exp_pos _).le
    refine (hT₀ t (hT.trans ht)).trans
      ((div_le_div_of_nonneg_left (by norm_num) (by positivity) hden).trans ?_)
    have he : Real.exp (-(T / 2)) = Real.exp ((1 / 2 - β) * T) *
        Real.exp ((β - 1) * T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hs : 3 / (Real.exp (T / 2) * T) = 3 * Real.exp (-(T / 2)) / T := by
      rw [Real.exp_neg]
      ring
    rw [hs, he, ← mul_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos _).le) hTpos.le
  have hexp (t : ℝ) (ht : T ≤ t) : 2 ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (hlog.trans ht)
  obtain ⟨⟨p, hp, hpJ⟩, ⟨m, hm, hmJ⟩⟩ := hpsiT
  have hscale : c * Real.exp ((β - 1) * T) / T =
      2 * ((c / 2) * Real.exp ((β - 1) * T) / T) := by ring
  rw [hscale] at hpJ hmJ
  constructor
  · refine ⟨p, hp, ?_⟩
    rw [neg_F_eq_Jpsi_sub_S (hexp p hp.1)]
    have hpS := (le_abs_self _).trans (hpay p hp.1)
    linarith only [hpJ, hpS]
  · refine ⟨m, hm, ?_⟩
    rw [neg_F_eq_Jpsi_sub_S (hexp m hm.1)]
    have hmS := (neg_le_abs _).trans (hpay m hm.1)
    linarith only [hmJ, hmS]

end D5.S3.Arith.Robin.Analytic.ActualUnattainedThetaWindows
