/- GID: D5/S3/Weil/Mertens/CriticalThetaTailPeak
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CriticalThetaTailPeak
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Critical-exponent amplitude of the actual signed theta tail. -/

import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import D5.S3.Analytic.Laplace.EulerPoleObstruction
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

end D5.S3.Weil.Mertens.CriticalThetaTailPeak
