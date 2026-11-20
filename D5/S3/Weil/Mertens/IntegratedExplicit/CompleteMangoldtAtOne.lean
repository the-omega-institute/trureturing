/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Removing a zeta pole from the completed Mangoldt transform gives uniform Cauchy bounds for every derivative on an isolated-zero disk, including disks crossing one. -/

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
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
        ‖iteratedDeriv n F p - c * ((-1 : ℂ)^n * n.factorial *
          (p-z)^(-1-(n : ℤ)))‖ ≤ (n.factorial : ℝ) * B / r^n := by
  let F := completed
  refine ⟨completed_analytic_unique, ?_⟩
  intro p z r hr hpz hz hball c
  have hz1 : z ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hz
  obtain ⟨_, _, H, hH, hprincipal⟩ :=
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
  refine ⟨max B 0, le_max_right _ _, fun n => ?_⟩
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

end D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
