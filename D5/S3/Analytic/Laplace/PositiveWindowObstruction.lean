/- GID: D5/S3/Analytic/Laplace/PositiveWindowObstruction
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/PositiveWindowObstruction
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: An eventual exponential upper bound and continuation across real cuts give absolute convergence of a signed Laplace tail. -/

import D5.S3.Analytic.Laplace.EulerPoleObstruction

/-! An eventual exponential upper bound turns a signed Laplace tail into a
positive measure. Local regularity of the actual tail rules out any convergence
cut to the right of the bound's exponent. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace D5.S3.Analytic.Laplace.PositiveWindowObstruction

open AbscissaSingularity
open EulerPoleObstruction (kernel tailLaplace finiteHead finiteHead_entire)

private theorem kernel_integrable_of_real_weight {g : ℝ → ℝ} {U : ℝ} {z : ℂ}
    (hm : AEStronglyMeasurable g (volume.restrict (Ioi U)))
    (hi : IntegrableOn (fun t => Real.exp (-z.re * t) * g t) (Ioi U)) :
    IntegrableOn (kernel g z) (Ioi U) := by
  have hk : Continuous (fun t : ℝ => Complex.exp (-z * (t : ℂ))) := by fun_prop
  refine hi.norm.mono'
    (hk.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)) ?_
  filter_upwards with t
  change ‖kernel g z t‖ ≤ ‖Real.exp (-z.re * t) * g t‖
  simp [kernel, norm_mul, Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs, Real.abs_exp]

/-- An eventual exponential upper bound and local holomorphic extensions imply
absolute convergence and analyticity of the actual tail on `σ < z.re`.
At each potential cut the extension hypothesis gets the absolute convergence
and analyticity already proved on the open half-plane to its right. -/
theorem integrable_and_analytic_of_eventually_le_exp {g : ℝ → ℝ} {U σ C : ℝ}
    (hσ : σ < 0)
    (hg : ∀ x : ℝ, 0 < x →
      IntegrableOn (fun t => Real.exp (-x * t) * g t) (Ioi U))
    (hbound : ∀ᶠ t : ℝ in atTop, g t ≤ C * Real.exp (σ * t))
    (hregular : ∀ c : ℝ, σ < c → c ≤ 0 →
      (∀ x : ℝ, c < x → IntegrableOn (fun t => Real.exp (-x * t) * g t) (Ioi U)) →
      AnalyticOnNhd ℂ (tailLaplace g U) {z | c < z.re} →
      ∃ R : ℝ, 0 < R ∧ ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H (Metric.ball (c : ℂ) R) ∧
        ∀ z ∈ Metric.ball (c : ℂ) R, c < z.re → H z = tailLaplace g U z) :
    (∀ x : ℝ, σ < x → IntegrableOn (fun t => Real.exp (-x * t) * g t) (Ioi U)) ∧
      AnalyticOnNhd ℂ (tailLaplace g U) {z | σ < z.re} := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hbound
  let V := max (max U 0) T
  have hUV : U ≤ V := (le_max_left U 0).trans (le_max_left _ _)
  have hV0 : 0 ≤ V := (le_max_right U 0).trans (le_max_left _ _)
  have hTV : T ≤ V := le_max_right _ _
  have hg1 := hg 1 zero_lt_one
  have reweight (x : ℝ) :
      (fun t => Real.exp ((1 - x) * t) * (Real.exp (-(1 : ℝ) * t) * g t)) =
        (fun t => Real.exp (-x * t) * g t) := by
    funext t
    rw [← mul_assoc, ← Real.exp_add,
      show (1 - x) * t + -(1 : ℝ) * t = -x * t by ring]
  have hgMeas : AEStronglyMeasurable g (volume.restrict (Ioi U)) := by
    have he : Continuous (fun t : ℝ => Real.exp ((1 - (0 : ℝ)) * t)) := by fun_prop
    have hm : AEStronglyMeasurable
        (fun t => Real.exp ((1 - (0 : ℝ)) * t) * (Real.exp (-(1 : ℝ) * t) * g t))
        (volume.restrict (Ioi U)) :=
      he.aestronglyMeasurable.mul hg1.aestronglyMeasurable
    rw [reweight 0] at hm
    simpa using hm
  have hgHead (x : ℝ) :
      IntegrableOn (fun t => Real.exp (-x * t) * g t) (Ioc U V) := by
    have he : Continuous (fun t : ℝ => Real.exp ((1 - x) * t)) := by fun_prop
    obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc U V)).exists_bound_of_continuousOn
      he.continuousOn
    have hb : ∀ᵐ t ∂volume.restrict (Ioc U V), ‖Real.exp ((1 - x) * t)‖ ≤ K := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hK t ⟨ht.1.le, ht.2⟩
    rw [← reweight x]
    exact (hg1.mono_set Ioc_subset_Ioi_self).bdd_mul he.aestronglyMeasurable hb
  have hHead : Differentiable ℂ (finiteHead g U V) :=
    finiteHead_entire (by simpa using hgHead 0)

  let envelope : ℝ → ℝ := fun t => C * Real.exp (σ * t)
  let w : ℝ → ℝ := fun t => envelope t - g t
  let ν : Measure ℝ := volume.restrict (Ioi V)
  let μ : Measure ℝ := ν.withDensity (fun t => ENNReal.ofReal (w t))
  have hwPos : ∀ᵐ t ∂ν, 0 ≤ w t := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := V))] with t ht
    exact sub_nonneg.mpr (hT t (hTV.trans ht.le))
  have hDensityMeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) ν := by
    have hEnv : Continuous envelope := by
      dsimp only [envelope]
      fun_prop
    have hm : AEMeasurable g ν :=
      hgMeas.aemeasurable.mono_measure (Measure.restrict_mono_set volume (Ioi_subset_Ioi hUV))
    exact (hEnv.aemeasurable.sub hm).ennreal_ofReal
  have hDensityLtTop : ∀ᵐ t ∂ν, ENNReal.ofReal (w t) < (⊤ : ENNReal) :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hXm : AEMeasurable (id : ℝ → ℝ) μ := measurable_id.aemeasurable
  have hX : ∀ᵐ t ∂μ, 0 ≤ (id : ℝ → ℝ) t := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := V))] with t ht
    exact hV0.trans ht.le
  have hDensityWeight (x : ℝ) :
      x ∈ convergenceSet id μ ↔
        IntegrableOn (fun t => Real.exp (-x * t) * w t) (Ioi V) := by
    change Integrable (fun t : ℝ => Real.exp (-x * t))
      (ν.withDensity (fun t => ENNReal.ofReal (w t))) ↔ _
    rw [integrable_withDensity_iff_integrable_smul₀' hDensityMeas hDensityLtTop
      (g := fun t : ℝ => Real.exp (-x * t))]
    apply integrable_congr
    filter_upwards [hwPos] with t ht
    simp [ENNReal.toReal_ofReal ht, smul_eq_mul, mul_comm]
  have hWeight {x : ℝ} (hx : σ < x) :
      x ∈ convergenceSet id μ ↔
        IntegrableOn (fun t => Real.exp (-x * t) * g t) (Ioi U) := by
    rw [hDensityWeight x]
    have he : IntegrableOn (fun t => Real.exp (-x * t) * envelope t) (Ioi V) := by
      have hEq : (fun t : ℝ => Real.exp (-x * t) * envelope t) =
          (fun t : ℝ => C * Real.exp ((σ - x) * t)) := by
        funext t
        dsimp only [envelope]
        rw [mul_left_comm, ← Real.exp_add,
          show -x * t + σ * t = (σ - x) * t by ring]
      rw [hEq]
      exact (integrableOn_exp_mul_Ioi (sub_neg.mpr hx) V).const_mul C
    constructor
    · intro hw
      have ht : IntegrableOn (fun t => Real.exp (-x * t) * g t) (Ioi V) := by
        have hEq : (fun t : ℝ => Real.exp (-x * t) * g t) =
            (fun t : ℝ => Real.exp (-x * t) * envelope t - Real.exp (-x * t) * w t) := by
          funext t
          dsimp only [w]
          ring
        rw [hEq]
        exact he.sub' hw
      rw [← Ioc_union_Ioi_eq_Ioi hUV]
      exact (hgHead x).union ht
    · intro hi
      have hEq : (fun t : ℝ => Real.exp (-x * t) * w t) =
          (fun t : ℝ => Real.exp (-x * t) * envelope t - Real.exp (-x * t) * g t) := by
        funext t
        dsimp only [w]
        ring
      rw [hEq]
      exact he.sub' (hi.mono_set (Ioi_subset_Ioi hUV))

  let E : ℂ → ℂ := fun z => (C : ℂ) *
    (-Complex.exp (((σ : ℂ) - z) * (V : ℂ)) / ((σ : ℂ) - z))
  have hE {z : ℂ} (hz : σ < z.re) : AnalyticAt ℂ E z := by
    have hn : (σ : ℂ) - z ≠ 0 := sub_ne_zero.mpr fun he =>
      (ne_of_lt hz) (by simpa only [Complex.ofReal_re] using congrArg Complex.re he)
    dsimp only [E]
    fun_prop (disch := simp [hn])
  have hFormula {z : ℂ} (hz : σ < z.re) (hi : z.re ∈ convergenceSet id μ) :
      tailLaplace g U z = E z + finiteHead g U V z - complexMGF id μ (-z) := by
    have hgi := kernel_integrable_of_real_weight (z := z) hgMeas ((hWeight hz).mp hi)
    have hgt := hgi.mono_set (Ioi_subset_Ioi hUV)
    have ha : ((σ : ℂ) - z).re < 0 := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using sub_neg.mpr hz
    have hEnvKernel :
        kernel envelope z = fun t : ℝ => (C : ℂ) * Complex.exp (((σ : ℂ) - z) * (t : ℂ)) := by
      funext t
      simp only [kernel, envelope, Complex.ofReal_mul, Complex.ofReal_exp]
      rw [mul_left_comm, ← Complex.exp_add,
        show -z * (t : ℂ) + (σ : ℂ) * (t : ℂ) = ((σ : ℂ) - z) * (t : ℂ) by ring]
    have hei : IntegrableOn (kernel envelope z) (Ioi V) := by
      rw [hEnvKernel]
      exact (integrableOn_exp_mul_complex_Ioi ha V).const_mul (C : ℂ)
    have heVal : tailLaplace envelope V z = E z := by
      change (∫ t in Ioi V, kernel envelope z t) =
        (C : ℂ) * (-Complex.exp (((σ : ℂ) - z) * (V : ℂ)) / ((σ : ℂ) - z))
      rw [hEnvKernel, integral_const_mul, integral_exp_mul_complex_Ioi ha V]
    have hGap : complexMGF id μ (-z) = tailLaplace w V z := by
      change (∫ t : ℝ, Complex.exp (-z * (t : ℂ))
        ∂ν.withDensity (fun t => ENNReal.ofReal (w t))) = ∫ t : ℝ, kernel w z t ∂ν
      rw [integral_withDensity_eq_integral_toReal_smul₀ hDensityMeas hDensityLtTop
        (fun t : ℝ => Complex.exp (-z * (t : ℂ)))]
      apply integral_congr_ae
      filter_upwards [hwPos] with t ht
      simp only [ENNReal.toReal_ofReal ht, Complex.real_smul, kernel, mul_comm]
    have hGapSub : tailLaplace w V z = tailLaplace envelope V z - tailLaplace g V z := by
      have hK : kernel w z = fun t : ℝ => kernel envelope z t - kernel g z t := by
        funext t
        simp only [kernel, w, Complex.ofReal_sub, mul_sub]
      change (∫ t in Ioi V, kernel w z t) =
        (∫ t in Ioi V, kernel envelope z t) - ∫ t in Ioi V, kernel g z t
      rw [hK, integral_sub hei hgt]
    have hsum := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hgi.mono_set Ioc_subset_Ioi_self) hgt
    rw [Ioc_union_Ioi_eq_Ioi hUV] at hsum
    change tailLaplace g U z = finiteHead g U V z + tailLaplace g V z at hsum
    rw [hsum, hGap, hGapSub, heVal]
    ring
  have hAnalytic {c : ℝ} (hc : σ ≤ c) (hright : Ioi c ⊆ convergenceSet id μ) :
      AnalyticOnNhd ℂ (tailLaplace g U) {z | c < z.re} := by
    intro z hz
    change c < z.re at hz
    have hG := PositiveEulerContinuation.analytic_laplace hright z hz
    apply (((hE (z := z) (hc.trans_lt hz)).add (hHead.analyticAt z)).sub hG).congr
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with y hy
    exact (hFormula (z := y) (hc.trans_lt hy) (hright hy)).symm

  have hUpper {s t : ℝ} (hs : s ∈ convergenceSet id μ) (hst : s ≤ t) :
      t ∈ convergenceSet id μ := by
    apply hs.mono'
    · exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-t * u))).aestronglyMeasurable
    · filter_upwards [hX] with u hu
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hst) hu)
  have hne : (convergenceSet id μ).Nonempty :=
    ⟨1, (hWeight (hσ.trans zero_lt_one)).mpr hg1⟩
  have hConv : Ioi σ ⊆ convergenceSet id μ := by
    intro x hx
    by_contra hfail
    have hboundBelow : ∀ s ∈ convergenceSet id μ, x ≤ s := by
      intro s hs
      by_contra hxs
      exact hfail (hUpper hs (le_of_lt (lt_of_not_ge hxs)))
    have hbdd : BddBelow (convergenceSet id μ) := ⟨x, hboundBelow⟩
    let c := sInf (convergenceSet id μ)
    have hxc : x ≤ c := le_csInf hne hboundBelow
    have hσc : σ < c := (show σ < x from hx).trans_le hxc
    have hc0 : c ≤ 0 := by
      by_contra h
      have hp : 0 < c / 2 := half_pos (lt_of_not_ge h)
      have hs : c / 2 ∈ convergenceSet id μ := (hWeight (hσ.trans hp)).mpr (hg _ hp)
      have hle : c ≤ c / 2 := csInf_le hbdd hs
      linarith
    have hright : Ioi c ⊆ convergenceSet id μ := by
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne (show c < t from ht)
      exact hUpper hs hst.le
    obtain ⟨R, hR, H, hH, hAgree⟩ := hregular c hσc hc0
      (fun x hx => (hWeight (hσc.trans hx)).mp (hright hx)) (hAnalytic hσc.le hright)
    have hnb : Metric.ball (c : ℂ) R ∩ {z : ℂ | σ < z.re} ∈ 𝓝 (c : ℂ) :=
      inter_mem (Metric.ball_mem_nhds _ hR)
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show σ < (c : ℂ).re by simpa only [Complex.ofReal_re] using hσc))
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnb
    let K : ℂ → ℂ := fun z => E z + finiteHead g U V z - H z
    have hK : DifferentiableOn ℂ K (Metric.ball (c : ℂ) r) := by
      have hEd : DifferentiableOn ℂ E (Metric.ball (c : ℂ) r) :=
        fun z hz => (hE (z := z) (hsub hz).2).differentiableAt.differentiableWithinAt
      exact (hEd.add hHead.differentiableOn).sub (hH.mono fun _ hz => (hsub hz).1)
    refine no_holomorphic_extension_at_abscissa hXm hX hne hbdd hr ⟨hK, ?_⟩
    intro z hz hzr
    dsimp only [K]
    rw [hAgree z (hsub hz).1 hzr, hFormula (z := z) (hsub hz).2 (hright hzr)]
    ring
  exact ⟨fun x hx => (hWeight hx).mp (hConv hx), hAnalytic le_rfl hConv⟩

end D5.S3.Analytic.Laplace.PositiveWindowObstruction
