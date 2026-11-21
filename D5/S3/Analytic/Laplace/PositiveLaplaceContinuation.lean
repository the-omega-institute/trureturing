/- GID: D5/S3/Analytic/Laplace/PositiveLaplaceContinuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/PositiveLaplaceContinuation
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [mathlib/module/Mathlib.Analysis.Meromorphic.Order]
   utility: none
   digest: A real-regular meromorphic continuation forces positive Laplace convergence. -/

import D5.S3.Analytic.Laplace.EulerPoleObstruction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Extension of a positive Laplace integral across a real-regular meromorphic corridor. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology

namespace D5.S3.Analytic.Laplace.PositiveLaplaceContinuation

open AbscissaSingularity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- An initially convergent positive Laplace transform converges throughout a
meromorphic continuation half-plane if the continuation is analytic at all real
points where the convergence boundary could lie. Agreement near one point to
the right of both thresholds determines the continuation as a meromorphic germ
throughout the half-plane and determines its value at every point of continuity. -/
theorem integrable_and_analytic_of_meromorphic_continuation
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {a b : ℝ} (hb : Integrable (fun ω => Real.exp (-b * X ω)) μ)
    {H : ℂ → ℂ} (hHm : MeromorphicOn H {z | a < z.re})
    (hHa : ∀ x : ℝ, a < x → x ≤ b → AnalyticAt ℂ H (x : ℂ))
    {z₀ : ℂ} (ha₀ : a < z₀.re) (hb₀ : b < z₀.re)
    (hAgree : H =ᶠ[𝓝 z₀] fun z => complexMGF X μ (-z)) :
    (∀ x : ℝ, a < x → Integrable (fun ω => Real.exp (-x * X ω)) μ) ∧
    AnalyticOnNhd ℂ (fun z => complexMGF X μ (-z)) {z | a < z.re} ∧
    ∀ z : ℂ, a < z.re →
      Integrable (fun ω => Complex.exp (-z * (X ω : ℂ))) μ ∧
      (H =ᶠ[𝓝[≠] z] fun w => complexMGF X μ (-w)) ∧
      (ContinuousAt H z → H z = complexMGF X μ (-z)) := by
  let L : ℂ → ℂ := fun z => complexMGF X μ (-z)
  let D : ℂ → ℂ := fun z => H z - L z
  have hD₀ : meromorphicOrderAt D z₀ = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hAgree.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  have hGerm {c : ℝ} (hac : a ≤ c) (hc₀ : c < z₀.re)
      (hL : AnalyticOnNhd ℂ L {z | c < z.re}) {z : ℂ} (hz : c < z.re) :
      H =ᶠ[𝓝[≠] z] L := by
    have hHm' : MeromorphicOn H {w : ℂ | c < w.re} :=
      fun w hw => hHm w (hac.trans_lt hw)
    have hDm : MeromorphicOn D {w | c < w.re} := hHm'.sub hL.meromorphicOn
    have hTop := hDm.meromorphicOrderAt_eq_top_of_isPreconnected
      (convex_halfSpace_re_gt c).isPreconnected hc₀ hz hD₀
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hTop] with w hw
    exact sub_eq_zero.mp hw
  have hValue {z : ℂ} (h : H =ᶠ[𝓝[≠] z] L) (hH : ContinuousAt H z)
      (hL : ContinuousAt L z) : H z = L z :=
    tendsto_nhds_unique (hH.tendsto.mono_left nhdsWithin_le_nhds)
      ((hL.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)
  have hUpper {s t : ℝ} (hs : s ∈ convergenceSet X μ) (hst : s ≤ t) :
      t ∈ convergenceSet X μ := by
    apply hs.mono'
    · have hm : AEMeasurable (fun ω => Real.exp (-t * X ω)) μ := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [hX] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hst) hω)
  have hConv : ∀ x : ℝ, a < x → x ∈ convergenceSet X μ := by
    intro x hax
    by_contra hx
    have hne : (convergenceSet X μ).Nonempty := ⟨b, hb⟩
    have hbound : ∀ s ∈ convergenceSet X μ, x ≤ s := by
      intro s hs
      by_contra hxs
      exact hx (hUpper hs (le_of_lt (lt_of_not_ge hxs)))
    have hbdd : BddBelow (convergenceSet X μ) := ⟨x, hbound⟩
    let σ := sInf (convergenceSet X μ)
    have haσ : a < σ := hax.trans_le (le_csInf hne hbound)
    have hσb : σ ≤ b := csInf_le hbdd hb
    have hright : Ioi σ ⊆ convergenceSet X μ := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
      exact hUpper hs hst.le
    have hL : AnalyticOnNhd ℂ L {z | σ < z.re} :=
      PositiveEulerContinuation.analytic_laplace hright
    obtain ⟨r, hr, hrH⟩ := Metric.mem_nhds_iff.mp (hHa σ haσ hσb).eventually_analyticAt
    have hEq : EqOn H L (Metric.ball (σ : ℂ) r ∩ {z | σ < z.re}) := by
      intro z hz
      exact hValue (hGerm haσ.le (hσb.trans_lt hb₀) hL hz.2)
        (hrH hz.1).continuousAt (hL z hz.2).continuousAt
    exact no_holomorphic_extension_at_abscissa hXm hX hne hbdd hr
      ⟨fun z hz => (hrH hz).differentiableAt.differentiableWithinAt,
        fun z hz hzr => hEq ⟨hz, hzr⟩⟩
  have hL : AnalyticOnNhd ℂ L {z | a < z.re} :=
    PositiveEulerContinuation.analytic_laplace (fun _ hx => hConv _ hx)
  refine ⟨hConv, hL, fun z hz => ?_⟩
  have hi : Integrable (fun ω => Complex.exp (-z * (X ω : ℂ))) μ := by
    have hm : AEStronglyMeasurable (fun ω => Complex.exp (-z * (X ω : ℂ))) μ := by
      fun_prop
    apply (integrable_norm_iff hm).mp
    simpa only [Complex.norm_exp, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      using (show Integrable (fun ω => Real.exp (-z.re * X ω)) μ from hConv z.re hz)
  have h := hGerm le_rfl ha₀ hL hz
  exact ⟨hi, h, fun hH => hValue h hH (hL z hz).continuousAt⟩

#print axioms integrable_and_analytic_of_meromorphic_continuation

open EulerPoleObstruction (finiteHead finiteHead_entire kernel tailLaplace)

private lemma affine_damped_integrable (A B : ℝ) {τ d : ℝ} (hτ : 0 ≤ τ) (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => Real.exp (-d * t) * (A * t + B)) (Ioi τ) := by
  have hlin : IntegrableOn (fun t : ℝ => t * Real.exp (-d * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := d)
        (by norm_num) one_pos hd)
  have hi : IntegrableOn
      (fun t : ℝ => A * (t * Real.exp (-d * t)) + B * Real.exp (-d * t)) (Ioi τ) :=
    ((hlin.mono_set (Ioi_subset_Ioi hτ)).const_mul A).add
      ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) τ).const_mul B)
  refine hi.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only [Pi.add_apply]
  ring

private lemma affine_kernel_integrable (A B a : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    {s : ℂ} (hs : a < s.re) :
    IntegrableOn (kernel (fun t => A * t + B) (s - a)) (Ioi τ) := by
  have hcont : Continuous (kernel (fun t => A * t + B) (s - a)) := by
    unfold kernel
    fun_prop
  apply (integrable_norm_iff hcont.aestronglyMeasurable).mp
  convert (affine_damped_integrable A B hτ (sub_pos.mpr hs)).norm using 1
  funext t
  simp only [kernel, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

private def affineLaplace (A B τ a : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi τ, kernel (fun t => A * t + B) (s - a) t

private lemma affineLaplace_analytic (A B a : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (affineLaplace A B τ a) {s : ℂ | a < s.re} := by
  intro s hs
  change a < s.re at hs
  let d : ℝ := (s.re - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let g (t : ℝ) : ℝ := Real.exp (-d * t) * (A * t + B)
  have hg : IntegrableOn g (Ioi τ) := affine_damped_integrable A B hτ hd
  let shift (z : ℂ) : ℂ := (z - a) - (d : ℂ)
  have hf : affineLaplace A B τ a =
      (fun z => ∫ t in Ioi τ, kernel g z t) ∘ shift := by
    funext z
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [shift, g, kernel, Complex.ofReal_mul,
      Complex.ofReal_exp, Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hf]
  have hpos : 0 < (shift s).re := by
    dsimp only [shift]
    rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
    dsimp [d]
    linarith
  exact (EulerPoleObstruction.tail_analytic hg hτ (shift s) hpos).comp
    (f := shift) (x := s) ((analyticAt_id.sub analyticAt_const).sub analyticAt_const)

/-- An eventual affine majorant of a nonzero multiple of a continuous real
curve forces holomorphic continuation of its Laplace transform. The kernel uses
the spectral shift `s - a`, and the given meromorphic continuation must be
analytic at the real points to the right of `a`. -/
theorem analytic_continuation_of_affine_bound {f : ℝ → ℝ} {F : ℂ → ℂ}
    {a b U c A B : ℝ} (hU : 0 ≤ U) (hab : a < b) (hf : Continuous f) (hc : c ≠ 0)
    (h : ∀ᶠ t in atTop, c * f t ≤ A * t + B)
    (hi : ∀ s : ℂ, b < s.re → IntegrableOn (kernel f (s - a)) (Ioi U))
    (hF : ∀ s : ℂ, b < s.re → F s = tailLaplace f U (s - a))
    (hFm : MeromorphicOn F {s | a < s.re})
    (hFa : ∀ x : ℝ, a < x → AnalyticAt ℂ F (x : ℂ)) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L {s | a < s.re} ∧ ∀ s : ℂ, b < s.re → L s = F s := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp h
  let τ := max U R
  have hUτ : U ≤ τ := le_max_left _ _
  have hτ : 0 ≤ τ := hU.trans hUτ
  let r : ℝ := b + 1
  have hr : b < r := by dsimp [r]; linarith
  let w (t : ℝ) : ℝ := Real.exp (-(r - a) * t) * (A * t + B - c * f t)
  let μ : Measure ℝ := (volume.restrict (Ioi τ)).withDensity (fun t => ENNReal.ofReal (w t))
  have hw : IntegrableOn w (Ioi τ) := by
    have hcast : kernel f ((r : ℂ) - a) =
        (fun t : ℝ => ((Real.exp (-(r - a) * t) * f t : ℝ) : ℂ)) := by
      funext t
      simp only [kernel, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
        Complex.ofReal_sub]
    have hFr := hi (r : ℂ) (by simpa using hr)
    rw [hcast] at hFr
    have hReal : IntegrableOn (fun t : ℝ => Real.exp (-(r - a) * t) * f t) (Ioi U) :=
      (IntegrableOn.iff_ofReal (𝕜 := ℂ)).mpr hFr
    have hGap := (affine_damped_integrable A B hτ (sub_pos.mpr (hab.trans hr))).sub
      ((hReal.mono_set (Ioi_subset_Ioi hUτ)).const_mul c)
    refine hGap.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only [w, Pi.sub_apply]
    ring
  have hwpos : ∀ᵐ t ∂volume.restrict (Ioi τ), 0 ≤ w t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hR t
      ((le_max_right U R).trans ht.le)))
  let hμ : IsFiniteMeasure μ :=
    isFiniteMeasure_withDensity ((hasFiniteIntegral_iff_ofReal hwpos).mp hw.hasFiniteIntegral).ne
  have hX : ∀ᵐ t ∂μ, 0 ≤ id t := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hτ.trans ht.le
  have hb : Integrable (fun t : ℝ => Real.exp (-(0 : ℝ) * id t)) μ := by
    simp only [neg_zero, zero_mul, Real.exp_zero]
    exact integrable_const (μ := μ) (1 : ℝ)
  let P (s : ℂ) := finiteHead f U τ (s - a)
  have hP (s : ℂ) : AnalyticAt ℂ P s := by
    have he := finiteHead_entire (hf.integrableOn_Icc (a := U) (b := τ)
      |>.mono_set Ioc_subset_Icc_self)
    exact (he.analyticAt (s - a)).comp
      (f := fun z : ℂ => z - a) (x := s) (analyticAt_id.sub analyticAt_const)
  let K := affineLaplace A B τ a
  have hK : AnalyticOnNhd ℂ K {s : ℂ | a < s.re} := affineLaplace_analytic A B a hτ
  let shift (z : ℂ) := z + (r : ℂ)
  have hshift (z : ℂ) : AnalyticAt ℂ shift z := analyticAt_id.add analyticAt_const
  let H (z : ℂ) := K (shift z) - (c : ℂ) * (F (shift z) - P (shift z))
  have hHm : MeromorphicOn H {z | a - r < z.re} := by
    intro z hz
    change a - r < z.re at hz
    have hs : a < (shift z).re := by
      simp only [shift, Complex.add_re, Complex.ofReal_re]
      linarith
    have hdiff := (hFm _ hs).sub (hP _).meromorphicAt
    exact ((hK _ hs).meromorphicAt.sub
      ((MeromorphicAt.const (c : ℂ) _).mul hdiff)).comp_analyticAt (hshift z)
  have hHa (x : ℝ) (hx : a - r < x) : AnalyticAt ℂ H (x : ℂ) := by
    have hs : a < x + r := by linarith
    have he : shift (x : ℂ) = ((x + r : ℝ) : ℂ) := by simp [shift]
    have hp : AnalyticAt ℂ F (shift (x : ℂ)) := by rw [he]; exact hFa (x + r) hs
    have hz : a < (shift (x : ℂ)).re := by rwa [he, Complex.ofReal_re]
    exact ((hK _ hz).sub
      (analyticAt_const.mul (hp.sub (hP _)))).comp
        (f := shift) (x := (x : ℂ)) (hshift _)
  let M (z : ℂ) := ProbabilityTheory.complexMGF id μ (-z)
  have hmatch (z : ℂ) (hs : b < (shift z).re) : H z = M z := by
    have hA := affine_kernel_integrable A B a hτ (hab.trans hs)
    have hFull := hi (shift z) hs
    have hTail := hFull.mono_set (Ioi_subset_Ioi hUτ)
    have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hFull.mono_set Ioc_subset_Ioi_self) hTail
    rw [Ioc_union_Ioi_eq_Ioi hUτ] at hsplit
    change tailLaplace f U (shift z - a) = P (shift z) +
      (∫ t in Ioi τ, kernel f (shift z - a) t) at hsplit
    calc
      H z = (∫ t in Ioi τ,
          kernel (fun t => A * t + B) (shift z - a) t -
          (c : ℂ) * kernel f (shift z - a) t) := by
        dsimp only [H]
        rw [hF (shift z) hs, hsplit, integral_sub hA (hTail.const_mul (c : ℂ)),
          integral_const_mul]
        simp only [K, affineLaplace, add_sub_cancel_left]
      _ = M z := by
        dsimp only [M, ProbabilityTheory.complexMGF, μ]
        rw [integral_withDensity_eq_integral_toReal_smul₀ hw.aemeasurable.ennreal_ofReal
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards [hwpos] with t ht
        simp only [ENNReal.toReal_ofReal ht, id_eq, Complex.real_smul, w, kernel,
          Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_exp,
          Complex.ofReal_neg]
        have hexp : Complex.exp (-((r : ℂ) - a) * (t : ℂ)) *
            Complex.exp (-z * (t : ℂ)) = Complex.exp (-(shift z - a) * (t : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          dsimp only [shift]
          ring
        rw [← hexp]
        ring
  have hbase : b < (shift (1 : ℂ)).re := by
    simp only [shift, Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hAgree : H =ᶠ[𝓝 (1 : ℂ)] M := by
    have hopen : IsOpen {z : ℂ | b < (shift z).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp
        (show Continuous shift by dsimp only [shift]; fun_prop))
    filter_upwards [hopen.mem_nhds hbase] with z hz
    exact hmatch z hz
  obtain ⟨_, hM, _⟩ := integrable_and_analytic_of_meromorphic_continuation
    (X := id) measurable_id.aemeasurable hX hb hHm (fun x hx _ => hHa x hx)
    (z₀ := (1 : ℂ)) (by simp only [Complex.one_re]; linarith) (by norm_num) hAgree
  let unshift (s : ℂ) := s - (r : ℂ)
  let L (s : ℂ) := P s + (K s - M (unshift s)) / (c : ℂ)
  refine ⟨L, ?_, ?_⟩
  · intro s hs
    change a < s.re at hs
    have hu : a - r < (unshift s).re := by
      simpa only [unshift, Complex.sub_re, Complex.ofReal_re] using sub_lt_sub_right hs r
    have hm := (hM (unshift s) hu).comp (f := unshift) (x := s)
      (analyticAt_id.sub analyticAt_const)
    exact (hP s).add (((hK s hs).sub hm).div analyticAt_const (Complex.ofReal_ne_zero.mpr hc))
  · intro s hs
    have hshift_s : shift (unshift s) = s := sub_add_cancel s (r : ℂ)
    have hm := hmatch (unshift s) (by rwa [hshift_s])
    change K (shift (unshift s)) - (c : ℂ) *
      (F (shift (unshift s)) - P (shift (unshift s))) = M (unshift s) at hm
    rw [hshift_s] at hm
    dsimp only [L]
    rw [← hm]
    field_simp [Complex.ofReal_ne_zero.mpr hc]
    ring

#print axioms analytic_continuation_of_affine_bound

end D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
