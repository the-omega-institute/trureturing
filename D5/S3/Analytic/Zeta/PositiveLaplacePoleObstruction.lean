/- GID: D5/S3/Analytic/Zeta/PositiveLaplacePoleObstruction
   generality: I
   mirror-B: D5/B/S3/Analytic/Zeta/PositiveLaplacePoleObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positivity constrains the residues of a continued zeta Laplace transform. -/

import D5.S3.Analytic.Laplace.NonnegativeBoundary
import D5.S3.Analytic.Zeta.ZetaLogDerivativeRegularity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Positivity turns zeta residues into obstructions to one-sided Laplace budgets. -/

namespace D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction

open Set Filter MeasureTheory ProbabilityTheory ZetaAsymptotics
open D5.S3.Analytic.Zeta.ZetaLogDerivativeRegularity
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open scoped Topology

noncomputable section

private lemma far_left_interior {μ : Measure ℝ} {B t : ℝ}
    (hc : ∀ σ : ℝ, B < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    (ht : t < -B) : t ∈ interior (integrableExpSet id μ) := by
  apply mem_interior.mpr
  refine ⟨Iio (-B), ?_, isOpen_Iio, ht⟩
  intro u hu
  change u < -B at hu
  change Integrable (fun y : ℝ => Real.exp (u * y)) μ
  simpa only [neg_neg] using hc (-u) (by linarith)

/-- Multiplication by the normalized zeta factor propagates the initial
identity throughout the connected domain of actual transform convergence. -/
private theorem multiplied_identity {μ : Measure ℝ} {a B e k x0 : ℝ}
    (hx0 : 1 < x0) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R {s : ℂ | a < s.re})
    (hc : ∀ σ : ℝ, B < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    (hi : ∀ s : ℂ, max B (max a (1 / 2)) < s.re →
      complexMGF id μ (-s) = (e : ℂ) * regularizedPrincipal s + R s +
        (k : ℂ) * (x0 : ℂ) ^ (-s) / s)
    {s : ℂ} (hs : a < s.re)
    (hsi : (-s).re ∈ interior (integrableExpSet id μ)) :
    s * riemannZeta₁ (s + 1 / 2) * complexMGF id μ (-s) =
      -(e : ℂ) / 2 * s * deriv riemannZeta₁ (s + 1 / 2) +
        s * riemannZeta₁ (s + 1 / 2) * R s +
          (k : ℂ) * (x0 : ℂ) ^ (-s) * riemannZeta₁ (s + 1 / 2) := by
  let U : Set ℂ := {z : ℂ | (-z).re ∈ interior (integrableExpSet id μ)} ∩
    {z : ℂ | a < z.re}
  have hU : IsOpen U :=
    (isOpen_interior.preimage (Complex.continuous_re.comp continuous_neg)).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have hUc : IsPreconnected U := by
    exact ((convex_integrableExpSet.interior.linear_preimage (-Complex.reLm)).inter
      (convex_halfSpace_re_gt a)).isPreconnected
  let L : ℂ → ℂ := fun z => z * riemannZeta₁ (z + 1 / 2) * complexMGF id μ (-z)
  let H : ℂ → ℂ := fun z => -(e : ℂ) / 2 * z * deriv riemannZeta₁ (z + 1 / 2) +
    z * riemannZeta₁ (z + 1 / 2) * R z +
      (k : ℂ) * (x0 : ℂ) ^ (-z) * riemannZeta₁ (z + 1 / 2)
  have hZ (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => riemannZeta₁ (w + 1 / 2)) z :=
    (differentiable_riemannZeta₁.analyticAt (z + 1 / 2)).comp (f := fun w : ℂ => w + 1 / 2)
      (show AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z by fun_prop)
  have hZ' (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => deriv riemannZeta₁ (w + 1 / 2)) z :=
    (differentiable_riemannZeta₁.analyticAt (z + 1 / 2)).deriv.comp (f := fun w : ℂ => w + 1 / 2)
      (show AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z by fun_prop)
  have hP (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => (x0 : ℂ) ^ (-w)) z := by
    have hx : (x0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    exact ((differentiable_id.neg).const_cpow (.inl hx)).analyticAt z
  have hLa : AnalyticOnNhd ℂ L U := by
    intro z hz
    exact ((analyticAt_id.mul (hZ z)).mul
      ((analyticAt_complexMGF hz.1).comp
        (show AnalyticAt ℂ (fun w : ℂ => -w) z by fun_prop)))
  have hHa : AnalyticOnNhd ℂ H U := by
    intro z hz
    have hRz : AnalyticAt ℂ R z :=
      hR.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.2)
    exact (((analyticAt_const.mul analyticAt_id).mul (hZ' z)).add
      ((analyticAt_id.mul (hZ z)).mul hRz)).add
        ((analyticAt_const.mul (hP z)).mul (hZ z))
  let c : ℝ := max B (max a (1 / 2)) + 1
  have hcB : B < c := by dsimp [c]; linarith [le_max_left B (max a (1 / 2))]
  have hca : a < c := by dsimp [c]; linarith [le_max_right B (max a (1 / 2)), le_max_left a (1 / 2)]
  have hseed : (c : ℂ) ∈ U := by
    exact ⟨far_left_interior hc (by simpa using neg_lt_neg hcB), hca⟩
  have hEq : L =ᶠ[𝓝 (c : ℂ)] H := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show max B (max a (1 / 2)) < (c : ℂ).re by dsimp [c]; simp)] with z hz
    have hzhalf : 1 / 2 < z.re :=
      lt_of_le_of_lt ((le_max_right a _).trans (le_max_right B _)) hz
    have hz0 : z ≠ 0 := by
      intro h
      norm_num [h] at hzhalf
    have hzζ : riemannZeta₁ (z + 1 / 2) ≠ 0 := by
      intro h
      have hne := riemannZeta_ne_zero_of_one_lt_re
        (s := z + 1 / 2) (by simp only [Complex.add_re]; norm_num; linarith)
      apply hne
      rw [riemannZeta_eq_inv_sub_mul (by intro heq; have := congrArg Complex.re heq; simp at this; linarith), h, mul_zero]
    dsimp [L, H]
    rw [hi z hz]
    unfold regularizedPrincipal
    generalize hval : riemannZeta₁ (z + 1 / 2) = Z at hzζ ⊢
    field_simp [hzζ, hz0]
    <;> ring
  exact hLa.eqOn_of_preconnected_of_eventuallyEq hHa hUc hseed hEq ⟨hsi, hs⟩

private theorem identity_on_convergence {μ : Measure ℝ} {a B e k x0 : ℝ}
    (hx0 : 1 < x0) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R {s : ℂ | a < s.re})
    (hc : ∀ σ : ℝ, B < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    (hi : ∀ s : ℂ, max B (max a (1 / 2)) < s.re →
      complexMGF id μ (-s) = (e : ℂ) * regularizedPrincipal s + R s +
        (k : ℂ) * (x0 : ℂ) ^ (-s) / s)
    {s : ℂ} (hs : a < s.re) (hsi : (-s).re ∈ interior (integrableExpSet id μ))
    (hs0 : s ≠ 0) (hZ : riemannZeta₁ (s + 1 / 2) ≠ 0) :
    complexMGF id μ (-s) = (e : ℂ) * regularizedPrincipal s + R s +
      (k : ℂ) * (x0 : ℂ) ^ (-s) / s := by
  have h := multiplied_identity hx0 hR hc hi hs hsi
  unfold regularizedPrincipal
  generalize hval : riemannZeta₁ (s + 1 / 2) = Z at hZ h ⊢
  apply (mul_left_cancel₀ (mul_ne_zero hs0 hZ))
  field_simp [hs0, hZ] at h ⊢
  linear_combination h

/-- Positive Laplace integrals converge on every available positive real ray
where their continued zeta expression has no real singularity. -/
theorem laplace_integrable {μ : Measure ℝ} (hpos : ∀ᵐ y ∂μ, 0 ≤ y)
    {a B e k x0 : ℝ} (hx0 : 1 < x0) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R {s : ℂ | a < s.re})
    (hc : ∀ σ : ℝ, B < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    (hi : ∀ s : ℂ, max B (max a (1 / 2)) < s.re →
      complexMGF id μ (-s) = (e : ℂ) * regularizedPrincipal s + R s +
        (k : ℂ) * (x0 : ℂ) ^ (-s) / s) :
    ∀ σ : ℝ, max a 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ := by
  let U : Set ℂ := {z : ℂ | z.re < -(max a 0) ∧ riemannZeta₁ (-z + 1 / 2) ≠ 0}
  let F : ℂ → ℂ := fun z => (e : ℂ) * regularizedPrincipal (-z) + R (-z) +
    (k : ℂ) * (x0 : ℂ) ^ z / (-z)
  have hU : IsOpen U :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_ne_fun (differentiable_riemannZeta₁.continuous.comp (by fun_prop)) continuous_const)
  have hreal (t : ℝ) (ht : t < -(max a 0)) : (t : ℂ) ∈ U := by
    refine ⟨ht, ?_⟩
    have hσ : 0 ≤ -t := by linarith [le_max_right a (0 : ℝ)]
    have hZ := normalized_zeta_ne_zero_real (x := -t + 1 / 2) (by linarith)
    simpa using hZ
  have hF : DifferentiableOn ℂ F U := by
    intro z hz
    change z.re < -max a 0 ∧ _ at hz
    have ha : a < (-z).re := by simp only [Complex.neg_re]; linarith [le_max_left a (0 : ℝ)]
    have hRp := hR.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ha)
    have hZp := differentiable_riemannZeta₁.analyticAt (-z + 1 / 2)
    have hden : -z ≠ 0 := by
      intro heq
      have hzr : z.re = 0 := by simpa using congrArg Complex.re heq
      linarith [hz.1, le_max_right a (0 : ℝ)]
    have hxp : (x0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hpp : DifferentiableAt ℂ regularizedPrincipal (-z) :=
      (analyticAt_const.mul ((hZp.deriv.div hZp hz.2).comp (f := fun w : ℂ => w + 1 / 2)
        (show AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) (-z) by fun_prop))).differentiableAt
    exact (((hpp.comp z (differentiable_neg.differentiableAt)).const_mul _).add
      (hRp.comp z (differentiable_neg.differentiableAt))).add
        (((differentiableAt_id.const_cpow (.inl hxp)).const_mul _).div
          (differentiable_neg.differentiableAt) hden) |>.differentiableWithinAt
  have hinit : (integrableExpSet id μ).Nonempty :=
    ⟨-(B + 1), by
      change Integrable (fun y : ℝ => Real.exp (-(B + 1) * y)) μ
      exact hc (B + 1) (by linarith)⟩
  have hEq (t : ℝ) (ht : t < -(max a 0))
      (hti : t ∈ interior (integrableExpSet id μ)) :
      F =ᶠ[𝓝 (t : ℂ)] complexMGF id μ := by
    have hV := (isOpen_interior.preimage Complex.continuous_re).mem_nhds
      (show (t : ℂ).re ∈ interior (integrableExpSet id μ) from hti)
    filter_upwards [hU.mem_nhds (hreal t ht), hV] with z hz hzi
    change z.re < -max a 0 ∧ _ at hz
    have ha : a < (-z).re := by simp only [Complex.neg_re]; linarith [hz.1, le_max_left a (0 : ℝ)]
    have hz0 : -z ≠ 0 := by
      intro heq
      have hzr : z.re = 0 := by simpa using congrArg Complex.re heq
      linarith [hz.1, le_max_right a (0 : ℝ)]
    have heq := identity_on_convergence hx0 hR hc hi ha (by simpa using hzi) hz0 hz.2
    simpa only [F, neg_neg] using heq.symm
  intro σ hσ
  simpa only [neg_mul] using
    D5.S3.Analytic.Laplace.NonnegativeBoundary.integrable_exp_on_real_ray hpos hU hreal hF hinit hEq
      (-σ) (by linarith)

private lemma vanishing_factor {z0 : ℂ} {f : ℂ → ℂ} (hf : ContinuousAt f z0) :
    Tendsto (fun z : ℂ => (z - z0) * f z) (𝓝[≠] z0) (𝓝 0) := by
  have hid : Tendsto (fun z : ℂ => z - z0) (𝓝 z0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 z0) (𝓝 z0)).sub_const z0)
  simpa only [zero_mul] using (hid.mul hf.tendsto).mono_left nhdsWithin_le_nhds

private theorem continuation_residue {a e k x0 : ℝ} (hx0 : 1 < x0)
    {R : ℂ → ℂ} (hR : DifferentiableOn ℂ R {s : ℂ | a < s.re})
    {rho : ℂ} (hρ : IsNontrivialZero rho) (ha : a < (rho - 1 / 2).re)
    (h0 : rho - (1 / 2 : ℂ) ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ Tendsto (fun s : ℂ => (s - (rho - 1 / 2)) *
      ((e : ℂ) * regularizedPrincipal s + R s +
        (k : ℂ) * (x0 : ℂ) ^ (-s) / s))
      (𝓝[≠] (rho - 1 / 2)) (𝓝 (-(e : ℂ) * m / 2)) := by
  obtain ⟨m, hm, hlim⟩ := regularizedPrincipal_zero_residue hρ
  have hRc : ContinuousAt R (rho - 1 / 2) :=
    (hR.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ha)).continuousAt
  have hPc : ContinuousAt (fun s : ℂ => (k : ℂ) * (x0 : ℂ) ^ (-s) / s)
      (rho - 1 / 2) := by
    have hx : (x0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    fun_prop (disch := assumption)
  have hRlim : Tendsto (fun s : ℂ => (s - (rho - 1 / 2)) * R s)
      (𝓝[≠] (rho - 1 / 2)) (𝓝 0) := by
    exact vanishing_factor hRc
  have hPlim : Tendsto (fun s : ℂ => (s - (rho - 1 / 2)) *
      ((k : ℂ) * (x0 : ℂ) ^ (-s) / s))
      (𝓝[≠] (rho - 1 / 2)) (𝓝 0) := by
    exact vanishing_factor hPc
  refine ⟨m, hm, ?_⟩
  convert ((hlim.const_mul (e : ℂ)).add hRlim).add hPlim using 1
  · ext s
    ring
  · congr 1 <;> ring

/-- A positive nontrivial zero cannot lie inside the convergence half-plane
forced by positivity and real-axis regularity. -/
theorem no_positive_pole {μ : Measure ℝ} (hpos : ∀ᵐ y ∂μ, 0 ≤ y)
    {a B e k x0 : ℝ} (hx0 : 1 < x0) (he : |e| = 1) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R {s : ℂ | a < s.re})
    (hc : ∀ σ : ℝ, B < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    (hi : ∀ s : ℂ, max B (max a (1 / 2)) < s.re →
      complexMGF id μ (-s) = (e : ℂ) * regularizedPrincipal s + R s +
        (k : ℂ) * (x0 : ℂ) ^ (-s) / s)
    {rho : ℂ} (hρ : IsNontrivialZero rho) :
    rho.re - 1 / 2 ≤ max a 0 := by
  by_contra hn
  have hρgt : max a 0 < (rho - 1 / 2).re := by
    simpa using lt_of_not_ge hn
  have hρa : a < (rho - 1 / 2).re := (le_max_left _ _).trans_lt hρgt
  have hρ0 : rho - (1 / 2 : ℂ) ≠ 0 := by
    intro hz
    have hzre := congrArg Complex.re hz
    have : (0 : ℝ) < (rho - 1 / 2).re := (le_max_right _ _).trans_lt hρgt
    rw [hz] at this
    norm_num at this
  have hconv := laplace_integrable hpos hx0 hR hc hi
  have hsi : (-(rho - (1 / 2 : ℂ))).re ∈ interior (integrableExpSet id μ) :=
    far_left_interior hconv (by simpa using neg_lt_neg hρgt)
  have hLc : ContinuousAt (fun s : ℂ => complexMGF id μ (-s)) (rho - 1 / 2) :=
    ((analyticAt_complexMGF hsi).comp
      (show AnalyticAt ℂ (fun w : ℂ => -w) (rho - 1 / 2) by fun_prop)).continuousAt
  have hzero : Tendsto (fun s : ℂ =>
      (s - (rho - 1 / 2)) * complexMGF id μ (-s))
      (𝓝[≠] (rho - 1 / 2)) (𝓝 0) := by
    exact vanishing_factor hLc
  obtain ⟨m, hm, hres⟩ := continuation_residue hx0 hR hρ hρa hρ0
  have hevent : ∀ᶠ s : ℂ in 𝓝[≠] (rho - 1 / 2),
      complexMGF id μ (-s) = (e : ℂ) * regularizedPrincipal s + R s +
        (k : ℂ) * (x0 : ℂ) ^ (-s) / s := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (rho - 1 / 2), max a 0 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρgt
    filter_upwards [normalized_zeta_eventually_ne_zero hρ,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hgt] with s hZ hs
    have hs0 : s ≠ 0 := by intro hz; have := (le_max_right a (0 : ℝ)).trans_lt hs; simpa [hz] using this
    exact identity_on_convergence hx0 hR hc hi ((le_max_left _ _).trans_lt hs)
      (far_left_interior hconv (by simpa using neg_lt_neg hs)) hs0 hZ
  have hnonzero : -(e : ℂ) * m / 2 ≠ 0 := by
    have he0 : e ≠ 0 := by intro hz; simp [hz] at he
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr he0))
      (Nat.cast_ne_zero.mpr hm.ne')) two_ne_zero
  apply hnonzero
  exact (tendsto_nhds_unique (hzero.congr' (hevent.mono fun s hs => by rw [hs])) hres).symm

/-- A pole on the imaginary axis forces a one-sided budget of at least one half. -/
theorem critical_pole_budget {μ : Measure ℝ} (hpos : ∀ᵐ y ∂μ, 0 ≤ y)
    {a B e k x0 : ℝ} (hx0 : 1 < x0) (he : |e| = 1) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R {s : ℂ | a < s.re})
    (hc : ∀ σ : ℝ, B < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    (hi : ∀ s : ℂ, max B (max a (1 / 2)) < s.re →
      complexMGF id μ (-s) = (e : ℂ) * regularizedPrincipal s + R s +
        (k : ℂ) * (x0 : ℂ) ^ (-s) / s)
    (ha : a < 0) {rho : ℂ} (hρ : IsNontrivialZero rho) (hcrit : rho.re = 1 / 2) :
    (1 / 2 : ℝ) ≤ k := by
  let z0 : ℂ := rho - 1 / 2
  have hzre : z0.re = 0 := by dsimp [z0]; simp [Complex.sub_re, hcrit]
  have hz0 : z0 ≠ 0 := by
    intro heq
    have hρhalf : rho = (1 / 2 : ℂ) := by dsimp [z0] at heq; linear_combination heq
    have hne := D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.riemannZeta_ne_zero_of_real_mem_Ioo
      (1 / 2) (by norm_num) (by norm_num)
    apply hne
    simpa [hρhalf, D5.S3.Weil.Convention.classicalZeta] using hρ.1
  have hconv := laplace_integrable hpos hx0 hR hc hi
  have hzero : max a 0 = 0 := max_eq_right ha.le
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + z0) (𝓝[>] (0 : ℝ)) (𝓝[≠] z0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((Complex.continuous_ofReal.tendsto 0).add_const z0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change (σ : ℂ) + z0 ≠ z0
      intro heq
      have : (σ : ℂ) = 0 := add_right_cancel (heq.trans (zero_add z0).symm)
      exact (ne_of_gt hσ) (Complex.ofReal_eq_zero.mp this)
  obtain ⟨m, hm, hpole⟩ := continuation_residue hx0 hR hρ (by change a < z0.re; rw [hzre]; exact ha) hz0
  have hactual : Tendsto (fun σ : ℝ => (σ : ℂ) * complexMGF id μ (-((σ : ℂ) + z0)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(e : ℂ) * m / 2)) := by
    apply (hpole.comp hpath).congr'
    have hne0 : ∀ᶠ s : ℂ in 𝓝 z0, s ≠ 0 := compl_singleton_mem_nhds hz0
    filter_upwards [self_mem_nhdsWithin,
      hpath.eventually (normalized_zeta_eventually_ne_zero hρ),
      hpath.eventually (Filter.Eventually.filter_mono nhdsWithin_le_nhds hne0)]
      with σ hσ hZ hs0
    have hsre : max a 0 < ((σ : ℂ) + z0).re := by simpa [hzero, hzre] using hσ
    have heq := identity_on_convergence hx0 hR hc hi
      ((le_max_left _ _).trans_lt hsre)
      (far_left_interior hconv (by simpa using neg_lt_neg hsre)) hs0 hZ
    dsimp [z0] at *
    rw [heq]
    congr 1
    ring
  have hRc : ContinuousAt R (0 : ℂ) :=
    (hR.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using ha))).continuousAt
  have hPc : ContinuousAt regularizedPrincipal (0 : ℂ) :=
    (regularizedPrincipal_analyticAt_real (σ := 0) le_rfl).continuousAt
  have hx : (x0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hJ : ContinuousAt (fun s : ℂ => s * ((e : ℂ) * regularizedPrincipal s + R s) +
      (k : ℂ) * (x0 : ℂ) ^ (-s)) 0 := by fun_prop (disch := assumption)
  have hmass : Tendsto (fun σ : ℝ => (σ : ℂ) * complexMGF id μ (-(σ : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (k : ℂ)) := by
    have hlim := (hJ.tendsto.comp (Complex.continuous_ofReal.tendsto 0)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simp only [zero_mul, Complex.cpow_zero, neg_zero, mul_one, zero_add] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hs : max a 0 < σ := by simpa [hzero] using hσ
    have hs0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hσ)
    have hZ : riemannZeta₁ ((σ : ℂ) + 1 / 2) ≠ 0 := by
      simpa using normalized_zeta_ne_zero_real (x := σ + 1 / 2) (by linarith)
    rw [identity_on_convergence hx0 hR hc hi
      ((le_max_left _ _).trans_lt hs) (far_left_interior hconv (by simpa using neg_lt_neg hs)) hs0 hZ]
    dsimp only [Function.comp_def]
    field_simp [hs0]
    <;> ring
  have hle : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ),
      ‖(σ : ℂ) * complexMGF id μ (-((σ : ℂ) + z0))‖ ≤
        ((σ : ℂ) * complexMGF id μ (-(σ : ℂ))).re := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hbound := norm_complexMGF_le_mgf (X := id) (μ := μ) (z := -((σ : ℂ) + z0))
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, hzre, add_zero] at hbound
    have hr : (complexMGF id μ (-(σ : ℂ))).re = mgf id μ (-σ) := by
      rw [← Complex.ofReal_neg, re_complexMGF_ofReal]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hr]
    exact mul_le_mul_of_nonneg_left hbound hσ.le
  have hlimit := le_of_tendsto_of_tendsto hactual.norm
    ((Complex.continuous_re.tendsto _).comp hmass) hle
  have hn : ‖-(e : ℂ) * m / 2‖ = (m : ℝ) / 2 := by
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, he]
    simp
  rw [hn, Complex.ofReal_re] at hlimit
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hm)
  linarith

#print axioms laplace_integrable
#print axioms no_positive_pole
#print axioms critical_pole_budget

end
end D5.S3.Analytic.Zeta.PositiveLaplacePoleObstruction
