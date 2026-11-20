/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The completed Mangoldt transform recovers the residue of an isolated zeta zero from its normalized Taylor coefficients with a geometric rate and an eventual lower bound. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Set
open scoped Topology
open D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent (transform)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne

/-- The total transform with its removable singularity filled at one. -/
def completed : ℂ → ℂ :=
  Function.update transform 1 (1 + (Real.eulerMascheroniConstant : ℂ) - deriv (logDeriv riemannZeta₁) 1)

private lemma analytic_at_one : AnalyticAt ℂ completed 1 := by
  let A := logDeriv riemannZeta₁
  let D := {s : ℂ | riemannZeta₁ s ≠ 0}
  have hD : IsOpen D := isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  have h1 : (1 : ℂ) ∈ D := by simp [D]
  have ha : DifferentiableOn ℂ A D := by
    intro z hz
    exact ((differentiable_riemannZeta₁.analyticAt z).deriv.div
      (differentiable_riemannZeta₁.analyticAt z) hz).differentiableAt.differentiableWithinAt
  have hds : AnalyticAt ℂ (dslope A 1) 1 :=
    ((Complex.differentiableOn_dslope (hD.mem_nhds h1)).mpr ha).analyticAt (hD.mem_nhds h1)
  have hg : A 1 = (Real.eulerMascheroniConstant : ℂ) := by simp [A, logDeriv_apply]
  have hmodel : AnalyticAt ℂ (fun s : ℂ =>
      (1 + (Real.eulerMascheroniConstant : ℂ) - dslope A 1 s) / s) 1 :=
    (analyticAt_const.sub hds).div analyticAt_id one_ne_zero
  apply hmodel.congr
  have hne : ∀ᶠ z : ℂ in 𝓝 1, z ≠ 0 := continuousAt_id.eventually_ne one_ne_zero
  have hlog := eventually_nhdsWithin_iff.mp log_deriv_riemannZeta_eq_neg_inv_sub_add
  filter_upwards [hne, hlog] with s hs0 hlogS
  by_cases hs : s = 1
  · subst s
    simp [completed, dslope_same, A]
  · have hd := sub_ne_zero.mpr hs
    have hζ : deriv riemannZeta s / riemannZeta s = -(s-1)⁻¹ + A s := hlogS hs
    rw [dslope_of_ne _ hs, slope_def_field, hg, completed, Function.update_of_ne hs, transform,
      neg_div, hζ]
    push_cast
    field_simp [hs0, hd]
    ring

/-- Analyticity, value, and uniqueness of the completed function. -/
private theorem completed_analytic_unique :
    let F := completed
    (∀ s : ℂ, s ≠ 1 → F s = transform s) ∧
    F 1 = 1 + (Real.eulerMascheroniConstant : ℂ) - deriv (logDeriv riemannZeta₁) 1 ∧
    (∀ s : ℂ, s ≠ 0 → riemannZeta s ≠ 0 → AnalyticAt ℂ F s) ∧
    ∀ G : ℂ → ℂ, ContinuousAt G 1 → (∀ s : ℂ, s ≠ 1 → G s = transform s) → G = F := by
  have hoff (s : ℂ) (hs : s ≠ 1) : completed s = transform s :=
    Function.update_of_ne hs _ _
  refine ⟨hoff, Function.update_self .., ?_, ?_⟩
  · intro s hs0 hz
    by_cases hs1 : s = 1
    · simpa only [hs1] using analytic_at_one
    have hzeta := analyticAt_riemannZeta hs1
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have hd := sub_ne_zero.mpr hs1
    have ht : AnalyticAt ℂ transform s :=
      ((((hzeta.deriv.neg.div hzeta hz).div (analyticAt_id.mul hsub) (mul_ne_zero hs0 hd)).sub
        (analyticAt_const.div (hsub.pow 2) (pow_ne_zero 2 hd))).add (analyticAt_const.div hsub hd))
    exact ht.congr ((continuousAt_id.eventually_ne hs1).mono fun z h => (hoff z h).symm)
  · intro G hG hEq
    funext s
    by_cases hs : s = 1
    · subst s
      apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] (1 : ℂ))
        (hG.tendsto.mono_left nhdsWithin_le_nhds)
        (analytic_at_one.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin (α := ℂ) (a := 1) (s := ({1} : Set ℂ)ᶜ)] with z hz
      exact (hEq z hz).trans (hoff z hz).symm
    · exact (hEq s hs).trans (hoff s hs).symm

/-- Normalizing the signed complex derivatives removes the principal pole phase.
The same boundary constant supplies a geometric rate, the limit, and a
uniform eventual lower bound. -/
private lemma normalize_coefficients (q c : ℂ) (a : ℕ → ℂ) {r B : ℝ}
    (hq : q ≠ 0) (hc : c ≠ 0) (hr : 0 < r)
    (h : ∀ n : ℕ, ‖a n - c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))‖ ≤
      (n.factorial : ℝ) * B / r^n) :
    let J := fun n : ℕ => q^(n+1) * ((-1 : ℂ)^n / n.factorial) * a n
    (∀ n : ℕ, ‖J n - c‖ ≤ B * ‖q‖ * (‖q‖ / r)^n) ∧
    (‖q‖ < r → Tendsto J atTop (𝓝 c) ∧ ∀ᶠ n in atTop, ‖c‖ / 2 ≤ ‖J n‖) := by
  intro J
  have bound (n : ℕ) : ‖J n - c‖ ≤ B * ‖q‖ * (‖q‖ / r)^n := by
    let K := q^(n+1) * ((-1 : ℂ)^n / n.factorial)
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : q^(-1-(n : ℤ)) = (q^(n+1))⁻¹ := by
      rw [show (-1-(n : ℤ)) = -((n+1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hsign : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by rw [← mul_pow]; simp
    have cancel : K * (c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))) = c := by
      rw [hpow]
      dsimp only [K]
      field_simp [hn, hq]
      simpa only [pow_two] using hsign
    have herr : J n - c = K * (a n - c * ((-1 : ℂ)^n * n.factorial * q^(-1-(n : ℤ)))) := by
      rw [mul_sub, cancel]
    rw [herr, norm_mul]
    apply (mul_le_mul_of_nonneg_left (h n) (norm_nonneg K)).trans_eq
    dsimp only [K]
    simp only [norm_mul, norm_pow, norm_div, norm_neg, norm_one, one_pow, Complex.norm_natCast,
      div_pow, pow_succ]
    field_simp [hr.ne', Nat.factorial_ne_zero]
  refine ⟨bound, fun hqr => ?_⟩
  have hdecay := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (norm_nonneg q) hr.le) ((div_lt_one hr).mpr hqr)).const_mul (B * ‖q‖)
  have hlim : Tendsto J atTop (𝓝 c) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) bound (by simpa using hdecay)
  exact ⟨hlim, (hlim.norm.eventually (eventually_gt_nhds (half_lt_self (norm_pos_iff.mpr hc)))).mono
    fun n hn => hn.le⟩

/-- On a zero-isolating disk, subtracting the full pole leaves an analytic
function whose Taylor coefficients obey a single geometric bound. -/
theorem completed_disk_cauchy :
    let F := completed
    ((∀ s : ℂ, s ≠ 1 → F s = transform s) ∧
    F 1 = 1 + (Real.eulerMascheroniConstant : ℂ) - deriv (logDeriv riemannZeta₁) 1 ∧
    (∀ s : ℂ, s ≠ 0 → riemannZeta s ≠ 0 → AnalyticAt ℂ F s) ∧
    ∀ G : ℂ → ℂ, ContinuousAt G 1 → (∀ s : ℂ, s ≠ 1 → G s = transform s) → G = F) ∧
    ∀ (p z : ℂ) (r : ℝ), 0 < r → p ≠ z → riemannZeta z = 0 →
      (∀ w ∈ Metric.closedBall p r, w ≠ 0 ∧ (riemannZeta w = 0 → w = z)) →
      let c := (analyticOrderNatAt riemannZeta z : ℂ) / (z * (1-z))
      let J := fun n : ℕ => (p-z)^(n+1) * ((-1 : ℂ)^n / n.factorial) * iteratedDeriv n F p
      ∃ B : ℝ, 0 ≤ B ∧ (∀ n : ℕ,
        ‖iteratedDeriv n F p - c * ((-1 : ℂ)^n * n.factorial *
          (p-z)^(-1-(n : ℤ)))‖ ≤ (n.factorial : ℝ) * B / r^n) ∧
        (∀ n : ℕ, ‖J n - c‖ ≤ B * ‖p-z‖ * (‖p-z‖ / r)^n) ∧
        (‖p-z‖ < r → Tendsto J atTop (𝓝 c) ∧ ∀ᶠ n in atTop, ‖c‖ / 2 ≤ ‖J n‖) := by
  let F := completed
  refine ⟨completed_analytic_unique, ?_⟩
  intro p z r hr hpz hz hball c J
  have hz1 : z ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hz
  obtain ⟨_, hc0, H, hH, hprincipal⟩ :=
    D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaurent.transform_integral_and_zero_germs.2 z hz
  let P := fun s : ℂ => c / (s-z)
  let G := Function.update (fun s => F s - P s) z (H z)
  have hoff (s : ℂ) (hs : s ≠ z) : G s = F s - P s := Function.update_of_ne hs _ _
  have hgerm : G =ᶠ[𝓝 z] H := by
    have h := eventually_nhdsWithin_iff.mp hprincipal
    filter_upwards [h, continuousAt_id.eventually_ne hz1] with s he hs1
    by_cases hs : s = z
    · subst s
      exact Function.update_self ..
    · rw [hoff s hs]
      change completed s - c / (s-z) = H s
      rw [completed_analytic_unique.1 s hs1, he hs]
      dsimp only [c]
      ring
  have haP {s : ℂ} (hs : s ≠ z) : AnalyticAt ℂ P s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)
  have hmodel (s : ℂ) (hs : s ≠ z) : G =ᶠ[𝓝 s] fun w => F w - P w :=
    (continuousAt_id.eventually_ne hs).mono fun w hw => hoff w hw
  have haF {s : ℂ} (hs : s ∈ Metric.closedBall p r) (hsz : s ≠ z) : AnalyticAt ℂ F s :=
    completed_analytic_unique.2.2.1 s (hball s hs).1 (fun h => hsz ((hball s hs).2 h))
  have ha : AnalyticOnNhd ℂ G (Metric.closedBall p r) := by
    intro s hs
    by_cases hsz : s = z
    · subst s
      exact hH.congr hgerm.symm
    · exact ((haF hs hsz).sub (haP hsz)).congr (hmodel s hsz).symm
  obtain ⟨B, hB⟩ := (isCompact_closedBall p r).exists_bound_of_continuousOn ha.continuousOn
  have hraw (n : ℕ) :
      ‖iteratedDeriv n F p - c * ((-1 : ℂ)^n * n.factorial * (p-z)^(-1-(n : ℤ)))‖ ≤
        (n.factorial : ℝ) * max B 0 / r^n := by
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      (ha.differentiableOn.diffContOnCl_ball (Subset.rfl)) (fun w hw =>
        (hB w (Metric.sphere_subset_closedBall hw)).trans (le_max_left B 0))
    rw [(hmodel p hpz).iteratedDeriv_eq n, iteratedDeriv_fun_sub
      (haF (Metric.mem_closedBall_self hr.le) hpz).contDiffAt (haP hpz).contDiffAt] at hc
    have hP : iteratedDeriv n P p = c * ((-1 : ℂ)^n * n.factorial * (p-z)^(-1-(n : ℤ))) := by
      dsimp only [P]
      simp only [div_eq_mul_inv, iteratedDeriv_const_mul_field]
      rw [iteratedDeriv_comp_sub_const (f := Inv.inv), iteratedDeriv_eq_iterate]
      exact congrArg (c * ·) (iter_deriv_inv n (p-z))
    rwa [hP] at hc
  exact ⟨max B 0, le_max_right _ _, hraw,
    normalize_coefficients (p-z) c (fun n => iteratedDeriv n F p) (sub_ne_zero.mpr hpz) hc0 hr hraw⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
