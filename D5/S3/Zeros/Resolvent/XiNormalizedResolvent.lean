/- GID: D5/S3/Zeros/Resolvent/XiNormalizedResolvent
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/XiNormalizedResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identify the centered xi logarithmic derivative with its normalized zero resolvent. -/

import D5.S3.Analytic.XiGlobalGrowth
import D5.S3.Analytic.Dilation.ScalarUnitDressing
import D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
import D5.S3.Zeros.Endpoints.XiEndpointValues
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The finite divisor is cut off by the physical norm of rho. Its containing
spectral ball is enlarged by one half; it is not the shifted spectral cutoff.
Scaling preserves analytic multiplicity. Centering the Cf logarithmic derivative
and applying Schwarz gives a second inverse-radius factor after the chain rule.
The remainder decays like log(B_R)/R^2 for B_R = 2 exp(C (1+R)^(3/2)).
The combined rational summand is absolutely summable by comparison with the
actual shifted inverse-square zero sum; finite-cutoff limits identify its value.

Reuse: the existing Cf split/bound, scalar-unit dressing, analytic composition,
Schwarz, actual xi growth, and zero summability are applied directly. The pinned
product logarithmic-derivative theorem requires an identified locally uniform
product and is not by itself the actual xi identity. The sealed source search
covers fixed repository/library/open-change hits only; new external searches
were unavailable. Attribution is repository-derived, not a new literature audit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open Complex Filter Set Topology
open D5.S3.Zeros.CompletedZeta D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Analytic.Dilation.ScalarUnitDressing
open D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
open Zeta23.WeilEF

private theorem gamma_norm_le (rho : ℂ) : ‖Zeta23.gammaOf rho‖ ≤ ‖rho‖ + 1 / 2 := by
  simpa [Zeta23.gammaOf, norm_div] using norm_sub_le rho (1 / 2 : ℂ)

private noncomputable def cutoff (Z : ZeroData) (R : ℝ) : Finset ℕ :=
  (Z.symmetricIndices ((22 / 25) * R + 1 / 2)).filter (fun n => ‖Z.zero n‖ ≤ (22 / 25) * R)

private theorem mem_cutoff (Z : ZeroData) (R : ℝ) (n : ℕ) :
    n ∈ cutoff Z R ↔ ‖Z.zero n‖ ≤ (22 / 25) * R := by
  classical
  simp only [cutoff, Finset.mem_filter, Z.mem_symmetricIndices]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  have := gamma_norm_le (Z.zero n)
  rw [gammaOf_eq_spectralParameter] at this
  dsimp [ZeroData.gamma]
  linarith

private theorem cutoff_tendsto (Z : ZeroData) : Tendsto (cutoff Z) atTop atTop := by
  classical
  rw [tendsto_atTop]
  intro t
  filter_upwards [eventually_ge_atTop ((25 / 22 : ℝ) * ∑ n ∈ t, ‖Z.zero n‖)] with R hR
  intro n hn
  rw [mem_cutoff]
  have := Finset.single_le_sum (fun n _ => norm_nonneg (Z.zero n)) hn
  nlinarith

private theorem rational_tail (s rho : ℂ) (M : ℝ) (m : ℕ)
    (hs : ‖s‖ ≤ M) (hr : max 1 (2 * M) ≤ ‖rho‖) :
    ‖(m : ℂ) * (1 / (s - rho) + 1 / rho)‖ ≤
      8 * M * (m : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf rho)) := by
  have hr1 : 1 ≤ ‖rho‖ := (le_max_left _ _).trans hr
  have hrM : 2 * M ≤ ‖rho‖ := (le_max_right _ _).trans hr
  have hM : 0 ≤ M := (norm_nonneg s).trans hs
  have hr0 : 0 < ‖rho‖ := by linarith
  have hd : ‖rho‖ / 2 ≤ ‖s - rho‖ := by
    have := norm_sub_norm_le rho s
    rw [norm_sub_rev rho s] at this
    linarith
  have hd0 : 0 < ‖s - rho‖ := by linarith
  have he : 1 / (s - rho) + 1 / rho = s / ((s - rho) * rho) := by
    field_simp [norm_pos_iff.mp hr0, norm_pos_iff.mp hd0]; ring
  have hfirst : ‖(m : ℂ) * (1 / (s - rho) + 1 / rho)‖ ≤ 2 * M * (m : ℝ) / ‖rho‖ ^ 2 := by
    rw [he, norm_mul, norm_div, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (m : ℝ) * (M / ((‖rho‖ / 2) * ‖rho‖)) := by gcongr
      _ = _ := by ring
  have hg := gamma_norm_le rho
  have hden : 1 + Complex.normSq (Zeta23.gammaOf rho) ≤ 4 * ‖rho‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (Zeta23.gammaOf rho), sq_nonneg (‖rho‖ - 1)]
  have hdpos : 0 < 1 + Complex.normSq (Zeta23.gammaOf rho) := by
    linarith [Complex.normSq_nonneg (Zeta23.gammaOf rho)]
  apply hfirst.trans
  rw [div_le_div_iff₀ (sq_pos_of_pos hr0) hdpos]
  nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 2 * M * (m : ℝ) by positivity)]

private theorem rational_summable (Z : ZeroData) (s : ℂ) :
    Summable (fun n : ℕ => (Z.multiplicity n : ℂ) * (1 / (s - Z.zero n) + 1 / Z.zero n)) := by
  have h := (zeroEquiv Z).summable_iff.mpr (zero_sum_inv_sq Zeta23.zetaSeam)
  have hw : Summable (fun n => (Z.multiplicity n : ℝ) / 
      (1 + Complex.normSq (Zeta23.gammaOf (Z.zero n)))) := by
    convert h using 1
    funext n
    change _ = (Zeta23.zeroMult (Z.zero n) : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf (Z.zero n)))
    rw [multiplicity_eq_zeroMult]
  apply (hw.mul_left (8 * ‖s‖)).of_norm_bounded_eventually
  have he : ∀ᶠ n in cofinite, max 1 (2 * ‖s‖) ≤ ‖Z.zero n‖ := by
    have hf := Z.locallyFinite (max 1 (2 * ‖s‖) + 1 / 2)
    apply Filter.mem_cofinite.mpr
    apply hf.subset
    intro n hn
    have hn' : ‖Z.zero n‖ < max 1 (2 * ‖s‖) := not_le.mp hn
    have hh := gamma_norm_le (Z.zero n)
    rw [gammaOf_eq_spectralParameter] at hh
    change ‖spectralParameter (Z.zero n)‖ ≤ _
    linarith 
  filter_upwards [he] with n hn
  simpa [mul_div_assoc] using rational_tail s (Z.zero n) ‖s‖ (Z.multiplicity n) le_rfl hn

private theorem centered_cf {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) (hf0 : f 0 = 1)
    {B : ℝ} (hB : 2 ≤ B) (hfB : ∀ w, ‖w‖ ≤ 24 / 25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ < 83 / 100) :
    ‖logDeriv (Cf (22 / 25) f) z - logDeriv (Cf (22 / 25) f) 0‖ ≤
      (2 * (44795000 * Real.log B) / (83 / 100 : ℝ)) * ‖z‖ := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hfin := finite_SetOfZeros hfa hf0'
  have hc := CfAnalytic (by norm_num : (22 / 25 : ℝ) < 9 / 10) (by norm_num) hfa hf0'
  have hd : DifferentiableOn ℂ (logDeriv (Cf (22 / 25) f)) (Metric.ball 0 (83 / 100)) := by
    intro w hw
    have hw' : ‖w‖ < 83 / 100 := by simpa using hw
    have ha := hc w (by simpa using (show ‖w‖ ≤ 9 / 10 by linarith))
    exact (ha.deriv.div ha (Cf_ne_zero hfa hf0' (by norm_num) hfin
      (by linarith))).differentiableAt.differentiableWithinAt
  have hb (w : ℂ) (hw : ‖w‖ ≤ 83 / 100) := norm_logDeriv_Cf_le hfa hf0 hfin hB hfB hw
  have hm : MapsTo (logDeriv (Cf (22 / 25) f)) (Metric.ball 0 (83 / 100))
      (Metric.closedBall (logDeriv (Cf (22 / 25) f) 0) (2 * (44795000 * Real.log B))) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hw' : ‖w‖ ≤ 83 / 100 := le_of_lt (by simpa using hw)
    exact (norm_sub_le _ _).trans (by linarith [hb w hw', hb 0 (by norm_num)])
  simpa [dist_eq_norm] using Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm
    (show z ∈ Metric.ball 0 (83 / 100) by simpa using hz)
private def scaled (R : ℝ) (w : ℂ) := (2 : ℂ) * xiReading ((R : ℂ) * w)

private theorem scaled_analytic (R : ℝ) : AnalyticOnNhd ℂ (scaled R) (Metric.closedBall 0 1) :=
  fun _w _ => analyticAt_const.mul ((xi_reading_differentiable.analyticAt _).comp
    (analyticAt_const.mul analyticAt_id))

private theorem scaled_zero (R : ℝ) : scaled R 0 = 1 := by
  simp [scaled, D5.S3.Zeros.Endpoints.XiEndpointValues.xi_reading_endpoint_values.1]

private theorem xi_order (Z : ZeroData) (n : ℕ) :
    analyticOrderNatAt xiReading (Z.zero n) = Z.multiplicity n := by
  have hz := Z.zero_isNontrivial n
  have h0 : Z.zero n ≠ 0 := by intro h; simpa [h] using hz.2.1
  have h1 : Z.zero n ≠ 1 := by intro h; simpa [h] using hz.2.2
  have he : xiReading =ᶠ[𝓝 (Z.zero n)]
      (fun z : ℂ => ((1 / 2 : ℂ) * z * (z - 1)) * completedRiemannZeta z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0,
      isOpen_compl_singleton.mem_nhds h1] with z hz0 hz1
    exact xi_reading_eq_completed_zeta hz0 hz1
  have ho := (nonzero_scalar_dressing_preserves_zero_and_analytic_order
    (Zeta23.RvM.analyticAt_completedRiemannZeta h0 h1)
    (g := fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) (by fun_prop)
    (by exact mul_ne_zero (mul_ne_zero (by norm_num) h0) (sub_ne_zero.mpr h1))).2
  rw [analyticOrderNatAt, analyticOrderAt_congr he, ho]
  exact (Zeta23.RvM.analyticOrderNatAt_completedRiemannZeta hz.2.1 h1).trans
    (multiplicity_eq_zeroMult Z n).symm

private theorem scaled_order (Z : ZeroData) (R : ℝ) (hR : 0 < R) (n : ℕ) :
    analyticOrderNatAt (scaled R) (Z.zero n / (R : ℂ)) = Z.multiplicity n := by
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hd : deriv (fun w : ℂ => (R : ℂ) * w) (Z.zero n / (R : ℂ)) = R := by simp
  have hc := analyticOrderAt_comp_of_deriv_ne_zero (f := xiReading)
    (g := fun w : ℂ => (R : ℂ) * w) (z₀ := Z.zero n / (R : ℂ))
    (analyticAt_const.mul analyticAt_id) (by rw [hd]; exact hR')
  have hs := (nonzero_scalar_dressing_preserves_zero_and_analytic_order
    (f := fun w : ℂ => xiReading ((R : ℂ) * w)) (s := Z.zero n / (R : ℂ))
    ((xi_reading_differentiable.analyticAt _).comp (analyticAt_const.mul analyticAt_id))
    (g := fun _ : ℂ => (2 : ℂ)) analyticAt_const (by norm_num)).2
  unfold scaled analyticOrderNatAt
  rw [hs]
  change (analyticOrderAt (xiReading ∘ (fun w : ℂ => (R : ℂ) * w)) _).toNat = _
  rw [hc, mul_div_cancel₀ _ hR']
  exact xi_order Z n

private theorem scaled_logDeriv (R : ℝ) (w : ℂ) :
    logDeriv (scaled R) w = (R : ℂ) * logDeriv xiReading ((R : ℂ) * w) := by
  change logDeriv (fun z => (2 : ℂ) * xiReading ((R : ℂ) * z)) w = _
  rw [logDeriv_const_mul _ _ (by norm_num)]
  have hd := logDeriv_comp (xi_reading_differentiable ((R : ℂ) * w))
    (show DifferentiableAt ℂ (fun z : ℂ => (R : ℂ) * z) w by fun_prop)
  simpa [Function.comp_def, mul_comm] using hd

private theorem finite_split (Z : ZeroData) (R : ℝ) (hR : 0 < R) (s : ℂ)
    (hs : xiReading s ≠ 0) (hsR : ‖s / (R : ℂ)‖ < 22 / 25) :
    logDeriv xiReading s - logDeriv xiReading 0 =
      (∑ n ∈ cutoff Z R, (Z.multiplicity n : ℂ) * (1 / (s - Z.zero n) + 1 / Z.zero n)) + 
      (logDeriv (Cf (22 / 25) (scaled R)) (s / (R : ℂ)) -
        logDeriv (Cf (22 / 25) (scaled R)) 0) / (R : ℂ) := by
  classical
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hf0 : scaled R 0 ≠ 0 := by rw [scaled_zero]; exact one_ne_zero
  have hfin := finite_SetOfZeros (scaled_analytic R) hf0
  let T := (finiteSetOfZeros_mono (by norm_num : (22 / 25 : ℝ) < 1) hfin).toFinset
  have hmap (n : ℕ) : scaled R (Z.zero n / (R : ℂ)) = 0 := by
    simp only [scaled, mul_div_cancel₀ _ hR']
    have hh : xiReading (Z.zero n) = 0 :=
      (xiReading_eq_zero_iff_nontrivial _).mpr (zeroEquiv Z n).property
    rw [hh, mul_zero]
  have he : (∑ n ∈ cutoff Z R, (Z.multiplicity n : ℂ) * (1 / (s - Z.zero n) + 1 / Z.zero n)) =
      ∑ rho ∈ T, ((analyticOrderNatAt (scaled R) rho : ℂ) / (s / (R : ℂ) - rho) -
        (analyticOrderNatAt (scaled R) rho : ℂ) / (0 - rho)) / (R : ℂ) := by
    apply Finset.sum_bij (fun n _ => Z.zero n / (R : ℂ))
    · intro n hn
      change _ ∈ (finiteSetOfZeros_mono (by norm_num : (22 / 25 : ℝ) < 1) hfin).toFinset
      rw [Set.Finite.mem_toFinset]
      refine ⟨?_, hmap n⟩
      rw [norm_div, Complex.norm_of_nonneg hR.le, div_le_iff₀ hR]
      simpa [mul_comm] using (mem_cutoff Z R n).mp hn
    · intro a _ b _ hab
      exact Z.zero_injective ((div_left_inj' hR').mp hab)
    · intro rho hrho
      have hp : rho ∈ SetOfZeros (22 / 25) (scaled R) := by
        simpa only [T, Set.Finite.mem_toFinset] using hrho
      have hx : xiReading ((R : ℂ) * rho) = 0 := (mul_eq_zero.mp hp.2).resolve_left (by norm_num)
      obtain ⟨n, hn⟩ := (zeroEquiv Z).surjective
        ⟨(R : ℂ) * rho, (xiReading_eq_zero_iff_nontrivial _).mp hx⟩
      have hn' : Z.zero n = (R : ℂ) * rho := congrArg Subtype.val hn
      refine ⟨n, (mem_cutoff Z R n).mpr ?_, ?_⟩
      · rw [hn', norm_mul, Complex.norm_of_nonneg hR.le]
        nlinarith [mul_le_mul_of_nonneg_left hp.1 hR.le]
      · rw [hn']; field_simp
    · intro n _
      rw [scaled_order Z R hR]
      have hz0 : Z.zero n ≠ 0 := by
        intro hz; have := (Z.zero_isNontrivial n).2.1; simp [hz] at this
      have hsz : s - Z.zero n ≠ 0 := by
        intro hz; apply hs
        rw [sub_eq_zero.mp hz]
        exact (xiReading_eq_zero_iff_nontrivial _).mpr (zeroEquiv Z n).property
      have hszR : s / (R : ℂ) - Z.zero n / (R : ℂ) ≠ 0 := by
        rw [← sub_div]; exact div_ne_zero hsz hR'
      field_simp [hR', hz0, hsz, hszR]; ring
  have hs' : scaled R (s / (R : ℂ)) ≠ 0 := by
    simpa [scaled, mul_div_cancel₀ _ hR'] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hs
  have h1 := logDeriv_split (scaled_analytic R) hf0 (by norm_num : (22 / 25 : ℝ) < 1) hfin hsR hs'
  have h0 := logDeriv_split (scaled_analytic R) hf0 (by norm_num : (22 / 25 : ℝ) < 1) hfin
    (by norm_num : ‖(0 : ℂ)‖<22 / 25) hf0
  rw [scaled_logDeriv, mul_div_cancel₀ _ hR'] at h1
  rw [scaled_logDeriv, mul_zero] at h0
  rw [he, ← Finset.sum_div, Finset.sum_sub_distrib]
  change _ = ((∑ rho ∈ T, _) - (∑ rho ∈ T, _)) / (R : ℂ) + _
  change (R : ℂ) * logDeriv xiReading s = (∑ rho ∈ T, _) + _ at h1
  change (R : ℂ) * logDeriv xiReading 0 = (∑ rho ∈ T, _) + _ at h0
  apply (mul_right_cancel₀ hR')
  rw [add_mul, div_mul_cancel₀ _ hR', div_mul_cancel₀ _ hR']
  linear_combination h1 - h0

private theorem physical_error (C : ℝ) (hC : 0 < C)
    (hg : ∀ z, ‖xiReading z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)))
    (R M : ℝ) (hR : max 1 (2 * M) ≤ R) (s : ℂ) (hs : ‖s‖ ≤ M) :
    ‖(logDeriv (Cf (22 / 25) (scaled R)) (s / (R : ℂ)) -
      logDeriv (Cf (22 / 25) (scaled R)) 0) / (R : ℂ)‖ ≤
      (2 * 44795000 / (83 / 100 : ℝ)) *
        Real.log (2 * Real.exp (C * (1 + R) ^ (3 / 2 : ℝ))) * ‖s‖ / R ^ 2 := by
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRM : 2 * M ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hz : ‖s / (R : ℂ)‖ < 83 / 100 := by
    rw [norm_div, Complex.norm_of_nonneg hR0.le, div_lt_iff₀ hR0]
    linarith
  have hB : 2 ≤ 2 * Real.exp (C * (1 + R) ^ (3 / 2 : ℝ)) := by
    have := Real.one_le_exp (show 0 ≤ C * (1 + R) ^ (3 / 2 : ℝ) by positivity)
    linarith
  have hfB : ∀ w, ‖w‖ ≤ 24 / 25 → ‖scaled R w‖ ≤ 2 * Real.exp (C * (1 + R) ^ (3 / 2 : ℝ)) := by
    intro w hw
    have hwR : ‖(R : ℂ) * w‖ ≤ R := by
      rw [norm_mul, Complex.norm_of_nonneg hR0.le]; nlinarith
    simp only [scaled, norm_mul, Complex.norm_ofNat]
    apply mul_le_mul_of_nonneg_left ((hg _).trans ?_) (by norm_num)
    gcongr
  rw [norm_div, Complex.norm_of_nonneg hR0.le]
  calc
    _ ≤ ((2 * (44795000 * Real.log (2 * Real.exp (C * (1 + R) ^ (3 / 2 : ℝ)))) / (83 / 100 : ℝ)) *
      ‖s / (R : ℂ)‖) / R :=
      div_le_div_of_nonneg_right (centered_cf (scaled_analytic R) (scaled_zero R) hB hfB hz) hR0.le
    _ = _ := by rw [norm_div, Complex.norm_of_nonneg hR0.le]; ring

private theorem growth_decay (C : ℝ) (hC : 0 < C) :
    Tendsto (fun R : ℝ => Real.log (2 * Real.exp (C * (1 + R) ^ (3 / 2 : ℝ))) / R ^ 2)
      atTop (𝓝 0) := by
  have hn : ∀ᶠ R : ℝ in atTop, 0 ≤ Real.log (2 * Real.exp (C * (1 + R) ^ (3 / 2 : ℝ))) / R ^ 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    positivity
  apply squeeze_zero' hn ?_
    (show Tendsto (fun R : ℝ => (Real.log 2 + C * 2 ^ (3 / 2 : ℝ)) * R ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        (Real.log 2 + C * 2 ^ (3 / 2 : ℝ)))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp, add_div, mul_div_assoc]
  have hp : (1 + R) ^ (3 / 2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hR0.le]
    apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hpow : R ^ (3 / 2 : ℝ) / R ^ 2 = R ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hR0]; norm_num
  have hsmall : 1 / R ^ 2 ≤ R ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hR0.le]
    exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hdiv := div_le_div_of_nonneg_right hp (sq_nonneg R)
  rw [mul_div_assoc, hpow] at hdiv
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsmall' : Real.log 2 / R ^ 2 ≤ Real.log 2 * R ^ (-(1 / 2 : ℝ)) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hsmall hlog
  nlinarith [mul_le_mul_of_nonneg_left hdiv hC.le]

/-- The centered logarithmic derivative of xi is its normalized zero resolvent. -/
theorem xi_reading_normalized_resolvent_hasSum
    (Z : D5.S3.Weil.ZeroSum.ZeroData) (s : ℂ)
    (hs : D5.S3.Zeros.CompletedZeta.xiReading s ≠ 0) :
    HasSum
      (fun n : ℕ =>
        (Z.multiplicity n : ℂ) * 
          (1 / (s - Z.zero n) + 1 / Z.zero n))
      (logDeriv D5.S3.Zeros.CompletedZeta.xiReading s -
        logDeriv D5.S3.Zeros.CompletedZeta.xiReading 0) := by
  obtain ⟨C, hC, hg⟩ := D5.S3.Analytic.XiGlobalGrowth.xi_reading_norm_le_exp_three_halves
  let a := fun n : ℕ => (Z.multiplicity n : ℂ) * (1 / (s - Z.zero n) + 1 / Z.zero n)
  let e := fun R : ℝ => (logDeriv (Cf (22 / 25) (scaled R)) (s / (R : ℂ)) -
    logDeriv (Cf (22 / 25) (scaled R)) 0) / (R : ℂ)
  have he : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun R : ℝ =>
      (Real.log (2 * Real.exp (C * (1 + R) ^ (3 / 2 : ℝ))) / R ^ 2) * 
        ((2 * 44795000 / (83 / 100 : ℝ)) * ‖s‖))
    · filter_upwards [eventually_ge_atTop (max 1 (2 * ‖s‖))] with R hR
      exact (physical_error C hC hg R ‖s‖ hR s le_rfl).trans_eq (by ring)
    · simpa using (growth_decay C hC).mul_const ((2 * 44795000 / (83 / 100 : ℝ)) * ‖s‖)
  have ha : Summable a := rational_summable Z s
  have hl := (ha.hasSum.comp (cutoff_tendsto Z)).add he
  simp only [add_zero] at hl
  have hv : Tendsto (fun R : ℝ => (∑ n ∈ cutoff Z R, a n) + e R) atTop
      (𝓝 (logDeriv xiReading s - logDeriv xiReading 0)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max 1 (2 * ‖s‖))] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hRM : 2 * ‖s‖ ≤ R := (le_max_right _ _).trans hR
    have hR0 : 0 < R := by linarith
    exact finite_split Z R hR0 s hs (by
      rw [norm_div, Complex.norm_of_nonneg hR0.le, div_lt_iff₀ hR0]; linarith)
  have hval := tendsto_nhds_unique hl hv
  exact hval ▸ ha.hasSum

#print axioms xi_reading_normalized_resolvent_hasSum

end D5.S3.Zeros.Resolvent.XiNormalizedResolvent
