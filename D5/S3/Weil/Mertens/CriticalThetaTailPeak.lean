/- GID: D5/S3/Weil/Mertens/CriticalThetaTailPeak
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CriticalThetaTailPeak
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Critical-exponent amplitude of the actual signed theta tail. -/

import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Analytic.Laplace.WindowEulerPole
import D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign

/-! Arithmetic forcing for the common actual-tail coefficient obstruction. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology

namespace D5.S3.Weil.Mertens.CriticalThetaTailPeak

open D5.S3.Analytic.Laplace.EulerPoleObstruction

private def boundary (U : ℝ) (z : ℂ) : ℂ :=
  (U : ℂ) ^ 2 * (ActualThetaTailLaplace.f U : ℂ) * Complex.exp (-z * (U : ℂ))

private def forcing (U : ℝ) (z : ℂ) : ℂ :=
  -deriv (ThetaLaplaceContinuation.M U) z + ThetaLaplaceContinuation.M U z + boundary U z

private theorem forcing_meromorphic (U : ℝ) (hU : 0 ≤ U) :
    MeromorphicOn (forcing U) ThetaLaplaceContinuation.D := by
  have hm := (ThetaLaplaceContinuation.theta_laplace_continuation U hU).2.2.2.2.1
  exact (hm.deriv.neg.add hm).add (by intro z hz; exact (by unfold boundary; fun_prop :
    AnalyticAt ℂ (boundary U) z).meromorphicAt)

theorem normalized_zeta_real_ne_zero {x : ℝ} (hx : 0 < x) :
    riemannZeta₁ (x : ℂ) ≠ 0 := by
  by_cases hx1 : x = 1
  · subst x
    simp
  · have hs := D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign.riemannZeta_ofReal_sign hx hx1
    have hz : riemannZeta (x : ℂ) ≠ 0 := by
      intro hz
      rw [hz] at hs
      rcases hs.2 with h | h <;> simp only [zero_re] at h <;> linarith [h.2]
    intro hn
    apply hz
    rw [riemannZeta_eq_inv_sub_mul (by exact_mod_cast hx1), hn, mul_zero]

private theorem theta_M_real_analytic (U : ℝ) (hU : 0 ≤ U) {x : ℝ}
    (hx : -(1 / 2 : ℝ) < x) : AnalyticAt ℂ (ThetaLaplaceContinuation.M U) (x : ℂ) := by
  obtain ⟨hC, hA, _, _, _, hzero, _⟩ :=
    ThetaLaplaceContinuation.theta_laplace_continuation U hU
  by_cases hx0 : x = 0
  · subst x
    simpa using hzero
  have hn := normalized_zeta_real_ne_zero (by linarith : 0 < 1 + x)
  have hna : AnalyticAt ℂ (logDeriv riemannZeta₁) ((1 + x : ℝ) : ℂ) :=
    (differentiable_riemannZeta₁.analyticAt _).deriv.div
      (differentiable_riemannZeta₁.analyticAt _) hn
  have hcomp : AnalyticAt ℂ (fun z => logDeriv riemannZeta₁ (1 + z)) (x : ℂ) := by
    exact hna.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 + z) (x : ℂ))
      (by push_cast; ring)
  have hc : AnalyticAt ℂ (fun z => ThetaLaplaceContinuation.C (1 + z)) (x : ℂ) :=
    (hC (1 + (x : ℂ)) (by simp; linarith)).comp (by fun_prop)
  unfold ThetaLaplaceContinuation.M
  exact (((analyticAt_const.add hcomp).add hc).neg.div (by fun_prop)
    (by intro h; have hr := congrArg Complex.re h; simp at hr; linarith)).sub (hA.analyticAt _)

private theorem forcing_real_analytic (U : ℝ) (hU : 0 ≤ U) {x : ℝ}
    (hx : -(1 / 2 : ℝ) < x) : AnalyticAt ℂ (forcing U) (x : ℂ) := by
  have hm := theta_M_real_analytic U hU hx
  exact (hm.deriv.neg.add hm).add (by unfold boundary; fun_prop)

private theorem actual_tail_integrable {U : ℝ} (hU : ActualThetaTailLaplace.u₀ ≤ U) :
    IntegrableOn ActualThetaTailLaplace.f (Ioi U) :=
  ActualThetaTailLaplace.actual_theta_tail_laplace_ode.2.2.2.2.1.mono_set (Ioi_subset_Ioi hU)

private theorem actual_euler (U : ℝ) (hU : ActualThetaTailLaplace.u₀ ≤ U)
    {z : ℂ} (hz : 0 < z.re) : euler (ActualThetaTailLaplace.L U) z = forcing U z := by
  have hU0 : 0 ≤ U := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hU
  have hcont := ThetaLaplaceContinuation.theta_laplace_continuation U hU0
  have hqm : ThetaLaplaceContinuation.Q U =ᶠ[𝓝 z] ThetaLaplaceContinuation.M U := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact (hcont.2.2.2.1 w hw).2.1
  have he := ((ActualThetaTailLaplace.actual_theta_tail_laplace_ode).2.2.2.2.2.2.2.2.2 U hU).2 z hz
  simpa only [euler, forcing, boundary, hqm.deriv_eq, hqm.eq_of_nhds] using he.2.2.2

private theorem zeta_zero_nonreal {ρ : ℂ} (hβ : (1 / 2 : ℝ) < ρ.re)
    (hβ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) : ρ.im ≠ 0 := by
  intro him
  have hr : (ρ.re : ℂ) = ρ := by apply Complex.ext <;> simp [him]
  have hs := D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign.riemannZeta_ofReal_sign
    (by linarith : 0 < ρ.re) hβ1.ne
  rw [hr, hz] at hs
  rcases hs.2 with h | h <;> simp only [zero_re] at h <;> linarith [h.1, h.2]

/-- The full normalized forcing coefficient comes from the original local
Laurent formula, including the actual cutoff boundary term. -/
private theorem forcing_doublePole (U : ℝ) (hU : 0 ≤ U) {ρ : ℂ}
    (hβ : (1 / 2 : ℝ) < ρ.re) (hzero : riemannZeta ρ = 0) :
    DoublePole (forcing U) (ρ - 1) (-(analyticOrderNatAt riemannZeta ρ : ℂ) / ρ) := by
  let a := ρ - 1
  let α : ℂ := -(analyticOrderNatAt riemannZeta ρ : ℂ) / ρ
  obtain ⟨_, _, _, _, hα, J, hJ, _, hLaurent, _, _⟩ :=
    (ThetaLaplaceContinuation.theta_laplace_continuation U hU).2.2.2.2.2.2.2 ρ hβ hzero
  let W : ℂ → ℂ := fun z => J z - deriv J z + boundary U z
  have hW : AnalyticAt ℂ W a := (hJ.sub hJ.deriv).add (by unfold boundary; fun_prop)
  have hp : Tendsto (fun z : ℂ => z - a) (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
    simpa using ((tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 a) (𝓝 a)).sub_const a).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun z : ℂ => α + α * (z - a) + (z - a) ^ 2 * W z)
      (𝓝[≠] a) (𝓝 α) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hp)).add
      ((hp.pow 2).mul (hW.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  refine ⟨hα, ?_⟩
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, hLaurent] with z hz hTz
  have hza : z ≠ a := by simpa using hz
  have hd : z - a ≠ 0 := sub_ne_zero.mpr hza
  change -deriv (ThetaLaplaceContinuation.M U) z + ThetaLaplaceContinuation.M U z =
    α / (z - a) ^ 2 + α / (z - a) + J z - deriv J z at hTz
  change α + α * (z - a) + (z - a) ^ 2 * W z = (z - a) ^ 2 * forcing U z
  unfold forcing
  rw [hTz]
  dsimp only [W]
  field_simp
  ring

/-- Every genuine zero in the open right half of the critical strip forces
arbitrarily late positive peaks with the full critical exponent and exact
multiplicity coefficient. -/
theorem critical_theta_tail_peak {ρ : ℂ} (hβ : (1 / 2 : ℝ) < ρ.re)
    (hβ1 : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
    let m := analyticOrderNatAt riemannZeta ρ
    0 < m ∧ ρ.im ≠ 0 ∧
      ∀ c : ℝ, 0 ≤ c → c < (m : ℝ) / (‖ρ‖ * ‖ρ - 1‖) →
        ∀ T : ℝ, ∃ u : ℝ, max T (Real.log 2) < u ∧
          c < u * Real.exp ((1 - ρ.re) * u) * ActualThetaTailLaplace.f u := by
  dsimp only
  have hnonreal := zeta_zero_nonreal hβ hβ1 hzero
  have hmult := (ThetaLaplaceContinuation.theta_laplace_continuation 0 le_rfl).2.2.2.2.2.2.2
    ρ hβ hzero
  refine ⟨hmult.2.2.1, hnonreal, ?_⟩
  let σ := ρ.re - 1
  let a := ρ - 1
  let Λ : ℂ := -(analyticOrderNatAt riemannZeta ρ : ℂ) / ρ
  have hU : 0 < ActualThetaTailLaplace.u₀ := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hdσ : -(1 / 2 : ℝ) < σ := by dsimp [σ]; linarith
  have hσ : σ < 0 := by dsimp [σ]; linarith
  have ha : a.re = σ := by simp [a, σ]
  have him : a.im ≠ 0 := by simpa [a] using hnonreal
  have hreal : ∀ x : ℝ, σ ≤ x → x ≤ 0 →
      AnalyticAt ℂ (forcing ActualThetaTailLaplace.u₀) (x : ℂ) := by
    intro x hx _
    exact forcing_real_analytic _ hU.le (lt_of_lt_of_le hdσ hx)
  have hpole : DoublePole (forcing ActualThetaTailLaplace.u₀) a Λ :=
    forcing_doublePole _ hU.le hβ hzero
  have hpeak := signed_peaks
    (actual_tail_integrable le_rfl) hU hdσ hσ
    (forcing_meromorphic _ hU.le) hreal (fun z hz => actual_euler _ le_rfl hz)
    ha him hpole
  have hcoef : ‖Λ‖ / ‖a‖ =
      (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * ‖ρ - 1‖) := by
    dsimp only [Λ, a]
    rw [norm_div, norm_neg, Complex.norm_natCast, div_div]
  intro c hc hcA T
  obtain ⟨u, hu, hval⟩ := hpeak 1 (by norm_num) c hc (by rw [hcoef]; exact hcA) T
  refine ⟨u, hu, ?_⟩
  simpa only [σ, neg_sub, one_mul] using hval

open D5.S3.Analytic.Laplace
open EulerLocalContinuation (rightHalfDisk)
open ForwardWindowLaplace
  (forwardWindow tailLaplace_firstMoment_eq_neg_deriv neg_deriv_euler_of_first_moment)
open ActualThetaTailLaplace (actual_theta_tail_laplace_ode u₀)

private theorem actual_firstMoment_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * (t * ActualThetaTailLaplace.f t))
      (Ioi u₀) := by
  have hx' : 0 < (x : ℂ).re := by simpa only [Complex.ofReal_re] using hx
  have hm := (actual_theta_tail_laplace_ode.2.2.2.2.2.2.2.2.2 u₀ le_rfl).2 (x : ℂ) hx'
  have hreal := Complex.reCLM.integrable_comp (hm.1 1)
  have hcast (t : ℝ) :
      (t : ℂ) ^ (1 : ℕ) * Complex.exp (-(x : ℂ) * (t : ℂ)) *
          (ActualThetaTailLaplace.f t : ℂ) =
        ((Real.exp (-x * t) * (t * ActualThetaTailLaplace.f t) : ℝ) : ℂ) := by
    simp only [pow_one, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  simpa only [IntegrableOn, Complex.reCLM_apply, hcast, Complex.ofReal_re] using hreal

private theorem actual_firstMoment_eq_neg_deriv {z : ℂ} (hz : 0 < z.re) :
    tailLaplace (fun t => t * ActualThetaTailLaplace.f t) u₀ z =
      -deriv (ActualThetaTailLaplace.L u₀) z := by
  have h := (actual_theta_tail_laplace_ode.2.2.2.2.2.2.2.2.2 u₀ le_rfl).2 z hz
  exact tailLaplace_firstMoment_eq_neg_deriv (f := ActualThetaTailLaplace.f) (U := u₀) h.2.1

private theorem actual_firstMoment_euler {z : ℂ} (hz : 0 < z.re) :
    WindowEulerPole.firstMomentEuler
        (tailLaplace (fun t => t * ActualThetaTailLaplace.f t) u₀) z =
      -deriv (forcing u₀) z := by
  have hF := (actual_theta_tail_laplace_ode.2.2.2.2.2.2.2.2.2 u₀ le_rfl).1
  have hright : {w : ℂ | 0 < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hΦ : euler (ActualThetaTailLaplace.L u₀) =ᶠ[𝓝 z] forcing u₀ := by
    filter_upwards [hright] with w hw
    exact actual_euler u₀ le_rfl hw
  have hL : tailLaplace (fun t => t * ActualThetaTailLaplace.f t) u₀ =ᶠ[𝓝 z]
      -deriv (ActualThetaTailLaplace.L u₀) := by
    filter_upwards [hright] with w hw
    exact actual_firstMoment_eq_neg_deriv hw
  exact (neg_deriv_euler_of_first_moment (hF z hz) hΦ hL).symm

private theorem actual_tail_laplace_zero_limit (hU : 0 ≤ u₀) :
    Tendsto (fun x : ℝ => ActualThetaTailLaplace.L u₀ (x : ℂ)) (𝓝[Ioi 0] 0)
      (𝓝 (∫ t in Ioi u₀, (ActualThetaTailLaplace.f t : ℂ))) := by
  have hf : IntegrableOn ActualThetaTailLaplace.f (Ioi u₀) := actual_tail_integrable le_rfl
  let K (x t : ℝ) : ℂ :=
    Complex.exp (-(x : ℂ) * (t : ℂ)) * (ActualThetaTailLaplace.f t : ℂ)
  have hm : ∀ᶠ x : ℝ in 𝓝[Ioi 0] 0,
      AEStronglyMeasurable (K x) (volume.restrict (Ioi u₀)) := by
    apply Eventually.of_forall
    intro x
    have he : Continuous (fun t : ℝ => Complex.exp (-(x : ℂ) * (t : ℂ))) := by fun_prop
    exact he.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  have hb : ∀ᶠ x : ℝ in 𝓝[Ioi 0] 0,
      ∀ᵐ t ∂volume.restrict (Ioi u₀), ‖K x t‖ ≤ ‖ActualThetaTailLaplace.f t‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [K]
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) (hU.trans ht.le)))
  have hl : ∀ᵐ t ∂volume.restrict (Ioi u₀),
      Tendsto (fun x : ℝ => K x t) (𝓝[Ioi 0] 0)
        (𝓝 (ActualThetaTailLaplace.f t : ℂ)) := by
    apply Eventually.of_forall
    intro t
    have hcont : Continuous (fun x : ℝ => K x t) := by
      dsimp only [K]
      fun_prop
    simpa [K] using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  exact tendsto_integral_filter_of_dominated_convergence (fun t => ‖ActualThetaTailLaplace.f t‖)
    hm hb hf.norm hl

private theorem actual_firstMoment_extension_at_zero (hU : 0 ≤ u₀) :
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r) ∧
        EqOn H (tailLaplace (fun t => t * ActualThetaTailLaplace.f t) u₀)
          (rightHalfDisk 0 r) := by
  have hΦ : AnalyticAt ℂ (forcing u₀) 0 := by
    simpa only [Complex.ofReal_zero] using
      (forcing_real_analytic u₀ hU (x := 0) (by norm_num))
  obtain ⟨r, hr, hrΦ⟩ := Metric.mem_nhds_iff.mp hΦ.eventually_analyticAt
  have hR : DifferentiableOn ℂ (forcing u₀) (Metric.ball (0 : ℂ) r) :=
    fun z hz => (hrΦ hz).differentiableAt.differentiableWithinAt
  have hF := (actual_theta_tail_laplace_ode.2.2.2.2.2.2.2.2.2 u₀ le_rfl).1
  have hFright : DifferentiableOn ℂ (ActualThetaTailLaplace.L u₀) (rightHalfDisk 0 r) :=
    hF.differentiableOn.mono (fun _ hz => hz.2)
  have hODE : ∀ z ∈ rightHalfDisk 0 r, euler (ActualThetaTailLaplace.L u₀) z = forcing u₀ z :=
    fun z hz => actual_euler u₀ le_rfl (show 0 < z.re from hz.2)
  obtain ⟨δ, hδ, _, H, hH, hAgree, _⟩ :=
    EulerLocalContinuation.exists_extension_at_zero hr hR hFright hODE
      (actual_tail_laplace_zero_limit hU)
  have hOpen : IsOpen (rightHalfDisk 0 δ) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  refine ⟨δ, hδ, -deriv H, (hH.deriv Metric.isOpen_ball).neg, ?_⟩
  intro z hz
  change -deriv H z = _
  rw [hAgree.deriv hOpen hz]
  exact (actual_firstMoment_eq_neg_deriv hz.2).symm

private theorem forcing_neg_deriv_order (U : ℝ) (hU : 0 ≤ U) {ρ : ℂ}
    (hβ : (1 / 2 : ℝ) < ρ.re) (hzero : riemannZeta ρ = 0) :
    meromorphicOrderAt (-deriv (forcing U)) (ρ - 1) = (-3 : ℤ) := by
  let a := ρ - 1
  obtain ⟨_, _, _, _, _, H, _, _, _, _, hOrder⟩ :=
    (ThetaLaplaceContinuation.theta_laplace_continuation U hU).2.2.2.2.2.2.2 ρ hβ hzero
  have hBoundary : AnalyticAt ℂ (boundary U) a := by unfold boundary; fun_prop
  have hLt : meromorphicOrderAt
      (fun z => -deriv (ThetaLaplaceContinuation.M U) z + ThetaLaplaceContinuation.M U z) a <
        meromorphicOrderAt (boundary U) a := by
    rw [hOrder]
    have hNeg : ((-2 : ℤ) : WithTop ℤ) < 0 := by
      rw [← WithTop.coe_zero, WithTop.coe_lt_coe]
      norm_num
    exact hNeg.trans_le hBoundary.meromorphicOrderAt_nonneg
  have horder : meromorphicOrderAt (forcing U) a = (-2 : ℤ) := by
    change meromorphicOrderAt
      ((fun z => -deriv (ThetaLaplaceContinuation.M U) z + ThetaLaplaceContinuation.M U z) +
        boundary U) a = _
    exact (meromorphicOrderAt_add_eq_left_of_lt hBoundary.meromorphicAt hLt).trans hOrder
  change meromorphicOrderAt (-deriv (forcing U)) a = _
  rw [← meromorphicOrderAt_neg]
  have hcast : ((-2 : ℤ) : ℂ) ≠ 0 := by norm_num
  have hsub : (-2 : ℤ) - 1 = -3 := by norm_num
  simpa only [hsub] using meromorphicOrderAt_deriv_eq_sub_one hcast horder

/-- A genuine zero in the open right half of the critical strip forces the
first-moment forward window of any positive width to exceed every exponential
bound with exponent below the real part of the shifted zero at arbitrarily late times. -/
theorem actual_theta_tail_window_peak {ρ : ℂ} (hβ : (1 / 2 : ℝ) < ρ.re)
    (hzero : riemannZeta ρ = 0) {h σ : ℝ}
    (hh : 0 < h) (hσρ : σ < ρ.re - 1) (C T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ C * Real.exp (σ * t) <
      forwardWindow (fun v => v * ActualThetaTailLaplace.f v) h t := by
  let σ' := max σ (-(1 / 2 : ℝ))
  have hdσ' : -(1 / 2 : ℝ) ≤ σ' := le_max_right _ _
  have hβ1 : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hzero
  have hU : 0 ≤ u₀ := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hσa : σ' < (ρ - 1).re := by
    simpa only [Complex.sub_re, Complex.one_re] using
      max_lt hσρ (by linarith only [hβ] : -(1 / 2 : ℝ) < ρ.re - 1)
  have ha : (ρ - 1).re < 0 := by simpa only [Complex.sub_re, Complex.one_re, sub_neg] using hβ1
  have hreal : ∀ c : ℝ, σ' < c → c < 0 →
      AnalyticAt ℂ (-deriv (forcing u₀)) (c : ℂ) := by
    intro c hσc _
    exact (forcing_real_analytic u₀ hU (hdσ'.trans_lt hσc)).deriv.neg
  have hpole : meromorphicOrderAt (-deriv (forcing u₀)) (ρ - 1) < 0 := by
    rw [forcing_neg_deriv_order u₀ hU hβ hzero, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    norm_num
  have hNoBound := WindowEulerPole.no_eventually_le_exp_of_pole
    (g := fun v => v * ActualThetaTailLaplace.f v) (U := u₀) (σ := σ') (C := max C 0)
    (P := -deriv (forcing u₀)) (a := ρ - 1)
    hh (fun _ hx => actual_firstMoment_integrable hx)
    (fun z hz => (forcing_meromorphic u₀ hU).deriv.neg z (hdσ'.trans_lt hz))
    hreal (fun _ hz => actual_firstMoment_euler hz)
    (actual_firstMoment_extension_at_zero hU) hσa ha hpole
  have hPeaks : ∃ᶠ t : ℝ in atTop, max C 0 * Real.exp (σ' * t) <
      forwardWindow (fun v => v * ActualThetaTailLaplace.f v) h t := by
    simpa only [Filter.Frequently, not_lt] using hNoBound
  obtain ⟨t, ht, hpeak⟩ := frequently_atTop.mp hPeaks (max T 0)
  have ht₀ : 0 ≤ t := (le_max_right T 0).trans ht
  have hExp : Real.exp (σ * t) ≤ Real.exp (σ' * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) ht₀)
  refine ⟨t, (le_max_left T 0).trans ht, ?_⟩
  calc
    C * Real.exp (σ * t) ≤ max C 0 * Real.exp (σ * t) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (σ' * t) :=
      mul_le_mul_of_nonneg_left hExp (le_max_right C 0)
    _ < _ := hpeak

#print axioms actual_theta_tail_window_peak

end D5.S3.Weil.Mertens.CriticalThetaTailPeak
