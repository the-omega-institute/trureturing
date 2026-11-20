/- GID: D5/S3/Analytic/OriginalHalfBinomialSlitPeriod
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialSlitPeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ParametricIntegral]
   utility: none
   digest: The slit continuation and complementary ratio of the original period. -/

import D5.S3.Analytic.OriginalHalfBinomialWronskian
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The principal Euler integral extends the original period across its disk boundary. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology Interval ComplexConjugate

namespace D5.S3.Analytic.OriginalHalfBinomialSlitPeriod

open OriginalHalfBinomialPeriod (period)

def slitDomain : Set ℂ := {r | 1 - r ∈ Complex.slitPlane}

def doubleSlit : Set ℂ := slitDomain ∩ Complex.slitPlane

private def endpoint : ℝ := Real.pi / 2

private lemma endpoint_pos : 0 < endpoint := by
  unfold endpoint
  positivity

private def base (r : ℂ) (θ : ℝ) : ℂ := 1 - r * (Real.sin θ ^ 2 : ℝ)

private def kernel (r : ℂ) (θ : ℝ) : ℂ := base r θ ^ (-1 / 2 : ℂ)

/-- Euler's integral with the principal inverse square root. -/
def slitPeriod (r : ℂ) : ℂ :=
  (2 / (Real.pi : ℂ)) * ∫ θ in (0 : ℝ)..Real.pi / 2,
    (1 - r * (Real.sin θ ^ 2 : ℝ)) ^ (-1 / 2 : ℂ)

private lemma isOpen_slitDomain : IsOpen slitDomain :=
  Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

private lemma isOpen_doubleSlit : IsOpen doubleSlit :=
  isOpen_slitDomain.inter Complex.isOpen_slitPlane

private lemma mem_slitDomain (r : ℂ) :
    r ∈ slitDomain ↔ r.re < 1 ∨ r.im ≠ 0 := by
  change 1 - r ∈ Complex.slitPlane ↔ _
  simp [Complex.mem_slitPlane_iff, sub_pos]

private lemma base_mem {r : ℂ} (hr : r ∈ slitDomain) (θ : ℝ) :
    base r θ ∈ Complex.slitPlane := by
  have hs : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  rw [Complex.mem_slitPlane_iff]
  simp only [base, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add, zero_sub, neg_ne_zero]
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · simp [← hs0]
  rcases (mem_slitDomain r).1 hr with hr | hr
  · left
    have h := mul_lt_mul_of_pos_right hr hs0
    nlinarith [Real.sin_sq_le_one θ]
  · exact Or.inr (mul_ne_zero hr hs0.ne')

private lemma continuous_base : Continuous (fun p : ℂ × ℝ => base p.1 p.2) := by
  unfold base
  fun_prop

private lemma continuous_kernel {r : ℂ} (hr : r ∈ slitDomain) : Continuous (kernel r) := by
  exact (continuous_base.comp (continuous_const.prodMk continuous_id)).cpow
    continuous_const (base_mem hr)

private def kernelDeriv (r : ℂ) (θ : ℝ) : ℂ :=
  (-1 / 2 : ℂ) * base r θ ^ ((-1 / 2 : ℂ) - 1) * -(Real.sin θ ^ 2 : ℝ)

private lemma kernel_hasDerivAt {r : ℂ} (hr : r ∈ slitDomain) (θ : ℝ) :
    HasDerivAt (fun z => kernel z θ) (kernelDeriv r θ) r := by
  simpa [kernel, kernelDeriv, base] using
    (((hasDerivAt_id r).mul_const ((Real.sin θ ^ 2 : ℝ) : ℂ)).const_sub 1).cpow_const
      (c := (-1 / 2 : ℂ)) (base_mem hr θ)

private lemma continuousOn_kernelDeriv :
    ContinuousOn (fun p : ℂ × ℝ => kernelDeriv p.1 p.2) (slitDomain ×ˢ univ) := by
  unfold kernelDeriv
  exact (continuousOn_const.mul (continuous_base.continuousOn.cpow_const
    (fun p hp => base_mem hp.1 p.2))).mul (by fun_prop)

set_option maxHeartbeats 800000 in
-- Elaborating the dominated differentiation lemma uses the restricted interval measure.
theorem slitPeriod_differentiableAt {r : ℂ} (hr : r ∈ slitDomain) :
    DifferentiableAt ℂ slitPeriod r := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_slitDomain.mem_nhds hr)
  have hs : Metric.closedBall r (ε / 2) ⊆ slitDomain :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  let μ := volume.restrict (Ioc 0 endpoint)
  have hcompact : IsCompact (Metric.closedBall r (ε / 2) ×ˢ Icc 0 endpoint) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image
    (continuousOn_kernelDeriv.mono (Set.prod_mono hs (subset_univ _))).norm
  have hmeas : ∀ᶠ z in 𝓝 r, AEStronglyMeasurable (kernel z) μ :=
    (show ∀ᶠ z in 𝓝 r, z ∈ slitDomain from isOpen_slitDomain.mem_nhds hr).mono
      fun _ hz => (continuous_kernel hz).aestronglyMeasurable
  have hint : Integrable (kernel r) μ :=
    ((continuous_kernel hr).intervalIntegrable 0 endpoint).1
  have hdmeas : AEStronglyMeasurable (kernelDeriv r) μ := by
    have hc : Continuous (kernelDeriv r) := by
      unfold kernelDeriv
      have hb : Continuous (base r) := continuous_base.comp
        (continuous_const.prodMk continuous_id)
      exact (continuous_const.mul (hb.cpow continuous_const (base_mem hr))).mul (by fun_prop)
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ θ ∂μ, ∀ z ∈ Metric.closedBall r (ε / 2), ‖kernelDeriv z θ‖ ≤ C := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := endpoint))]
      with θ hθ z hz
    exact hC ⟨(z, θ), ⟨hz, Ioc_subset_Icc_self hθ⟩, rfl⟩
  have hdiff : ∀ᵐ θ ∂μ, ∀ z ∈ Metric.closedBall r (ε / 2),
      HasDerivAt (fun w => kernel w θ) (kernelDeriv z θ) z :=
    Filter.Eventually.of_forall fun θ z hz => kernel_hasDerivAt (hs hz) θ
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.closedBall_mem_nhds r (by positivity : 0 < ε / 2))
    hmeas hint hdmeas hbound (integrable_const C) hdiff
  have hp := hd.2.const_mul (2 / (Real.pi : ℂ))
  change DifferentiableAt ℂ (fun z => (2 / (Real.pi : ℂ)) *
    ∫ θ in (0 : ℝ)..endpoint, kernel z θ) r
  simpa only [intervalIntegral.integral_of_le endpoint_pos.le, μ] using hp.differentiableAt

theorem slitPeriod_analyticOnNhd : AnalyticOnNhd ℂ slitPeriod slitDomain :=
  (show DifferentiableOn ℂ slitPeriod slitDomain from fun _ hr =>
    (slitPeriod_differentiableAt hr).differentiableWithinAt).analyticOnNhd isOpen_slitDomain

private lemma real_kernel {r : ℝ} (hr : r < 1) (θ : ℝ) :
    kernel (r : ℂ) θ = ((1 / Real.sqrt (1 - r * Real.sin θ ^ 2) : ℝ) : ℂ) := by
  have hb : 0 < 1 - r * Real.sin θ ^ 2 := by
    have hs := Real.sin_sq_le_one θ
    rcases le_or_gt r 0 with hr0 | hr0
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hr0 (sq_nonneg (Real.sin θ))]
    · nlinarith [mul_le_mul_of_nonneg_left hs hr0.le]
  have he : base (r : ℂ) θ = ((1 - r * Real.sin θ ^ 2 : ℝ) : ℂ) := by simp [base]
  rw [kernel, he, show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, Complex.cpow_neg]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hb.le,
    ← Real.sqrt_eq_rpow, ← Complex.ofReal_inv, one_div]

/-- The original dominated sine-moment calculation supplies the real interval
used to identify the holomorphic Euler integral with the literal series. -/
private lemma slitPeriod_eq_period_real {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) :
    slitPeriod (r : ℂ) = period (r : ℂ) := by
  have h := (OriginalHalfBinomialIntegral.original_series_eq_integral r h₀ h₁).2.2
  change period (r : ℂ) = _ at h
  rw [h]
  change (2 / (Real.pi : ℂ)) * (∫ θ in (0 : ℝ)..endpoint, kernel (r : ℂ) θ) = _
  simp_rw [real_kernel h₁, intervalIntegral.integral_ofReal]
  push_cast
  rfl

private lemma ball_subset_slitDomain : Metric.ball (0 : ℂ) 1 ⊆ slitDomain := by
  intro r hr
  exact (mem_slitDomain r).2 (Or.inl ((Complex.re_le_norm r).trans_lt (by simpa using hr)))

private lemma frequently_ofReal_near (a : ℝ) {p : ℂ → Prop}
    (h : ∀ᶠ x : ℝ in 𝓝[>] a, p (x : ℂ)) :
    ∃ᶠ z : ℂ in 𝓝[≠] (a : ℂ), p z := by
  have ht : Tendsto ((↑) : ℝ → ℂ) (𝓝[>] a) (𝓝[≠] (a : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_compl_singleton_iff.mpr (Complex.ofReal_injective.ne (ne_of_gt hx))
  exact ht.frequently (h.frequently)

/-- Equality with the literal half-binomial-square power series on the full unit disk. -/
theorem slitPeriod_eq_period {r : ℂ} (hr : ‖r‖ < 1) : slitPeriod r = period r := by
  have hp : AnalyticOnNhd ℂ period (Metric.ball (0 : ℂ) 1) :=
    (show DifferentiableOn ℂ period (Metric.ball (0 : ℂ) 1) from fun _ hz =>
      (OriginalHalfBinomialPeriod.picard_fuchs (by simpa using hz)).1.differentiableWithinAt
    ).analyticOnNhd Metric.isOpen_ball
  have hf : ∃ᶠ z : ℂ in 𝓝[≠] 0, slitPeriod z = period z := by
    simpa using frequently_ofReal_near 0 (p := fun z => slitPeriod z = period z) (by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
        with x hx hx1
      exact slitPeriod_eq_period_real (le_of_lt hx) hx1)
  exact (slitPeriod_analyticOnNhd.mono ball_subset_slitDomain)
    |>.eqOn_of_preconnected_of_frequently_eq hp (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
      (Metric.mem_ball_self zero_lt_one) hf (by simpa using hr)


private lemma sqrt_re_pos {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (z ^ (1 / 2 : ℂ)).re := by
  rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hz), Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have harg := Complex.neg_pi_lt_arg z
  have harg' := lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hz)
  simp only [Complex.mul_im, Complex.log_im]
  norm_num
  constructor <;> linarith

private lemma half_cpow_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = z := by
  rw [← Complex.cpow_mul_nat]
  norm_num

private lemma inverse_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (z⁻¹).re := by
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr (by intro h; simp [h] at hz))

private lemma kernel_re_pos {r : ℂ} (hr : r ∈ slitDomain) (θ : ℝ) :
    0 < (kernel r θ).re := by
  rw [kernel, show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, Complex.cpow_neg]
  exact inverse_re_pos (sqrt_re_pos (base_mem hr θ))

private lemma integral_re (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ θ in (0 : ℝ)..endpoint, f θ).re = ∫ θ in (0 : ℝ)..endpoint, (f θ).re :=
  (Complex.reCLM.intervalIntegral_comp_comm (hf.intervalIntegrable 0 endpoint)).symm

theorem slitPeriod_re_pos {r : ℂ} (hr : r ∈ slitDomain) : 0 < (slitPeriod r).re := by
  have h := continuous_kernel hr
  change 0 < ((2 / (Real.pi : ℂ)) * ∫ θ in (0 : ℝ)..endpoint, kernel r θ).re
  rw [show (2 / (Real.pi : ℂ)) = ((2 / Real.pi : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, integral_re _ h]
  exact mul_pos (div_pos (by norm_num) Real.pi_pos)
    (intervalIntegral.integral_pos endpoint_pos (Complex.continuous_re.comp h).continuousOn
      (fun θ _ => (kernel_re_pos hr θ).le)
      ⟨0, ⟨le_rfl, endpoint_pos.le⟩, kernel_re_pos hr 0⟩)

theorem slitPeriod_ne_zero {r : ℂ} (hr : r ∈ slitDomain) : slitPeriod r ≠ 0 := by
  intro h
  simpa [h] using slitPeriod_re_pos hr

private lemma complement_mem {r : ℂ} (hr : r ∈ doubleSlit) : 1 - r ∈ slitDomain := by
  change 1 - (1 - r) ∈ Complex.slitPlane
  simpa using hr.2

private lemma kernel_pair_re_pos {r : ℂ} (hr : r ∈ doubleSlit) (α β : ℝ) :
    0 < (conj (kernel r α) * kernel (1 - r) β).re := by
  let s := Real.sin α ^ 2
  let t := Real.sin β ^ 2
  let y := r.im
  let U := conj (base r α ^ (1 / 2 : ℂ))
  let V := base (1 - r) β ^ (1 / 2 : ℂ)
  have hU : 0 < U.re := sqrt_re_pos (base_mem hr.1 α)
  have hV : 0 < V.re := sqrt_re_pos (base_mem (complement_mem hr) β)
  have hUsq : U ^ 2 = conj (base r α) := by
    dsimp only [U]
    rw [← map_pow, half_cpow_sq]
  have hVsq : V ^ 2 = base (1 - r) β := half_cpow_sq _
  have him (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by simp [pow_two, Complex.mul_im]; ring
  have hUi : U.im = y * s / (2 * U.re) := by
    apply (eq_div_iff (by positivity)).2
    have h := congrArg Complex.im hUsq
    simp only [him, base, Complex.conj_im, Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, zero_sub, neg_neg] at h
    dsimp [y, s]
    linarith
  have hVi : V.im = y * t / (2 * V.re) := by
    apply (eq_div_iff (by positivity)).2
    have h := congrArg Complex.im hVsq
    simp only [him, base, Complex.conj_im, Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, zero_sub, neg_neg] at h
    dsimp [y, t]
    linarith
  have him_sq : ((U * V) ^ 2).im = y * (s * (1 - t) + t) := by
    rw [mul_pow, hUsq, hVsq]
    simp only [base, y, s, t, Complex.conj_im, Complex.conj_re, Complex.mul_im,
      Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, sub_zero, zero_sub]
    ring
  have hprod : 0 < (U * V).re := by
    by_cases h : y = 0 ∨ (s = 0 ∧ t = 0)
    · have hzero : U.im = 0 ∧ V.im = 0 := by
        rcases h with hy | ⟨hs, ht⟩
        · simp [hUi, hVi, hy]
        · simp [hUi, hVi, hs, ht]
      simpa [Complex.mul_re, hzero.1, hzero.2] using mul_pos hU hV
    · push Not at h
      have hs : 0 ≤ s := sq_nonneg _
      have ht : 0 ≤ t := sq_nonneg _
      have ht1 : t ≤ 1 := Real.sin_sq_le_one β
      have hcoef : 0 < s * (1 - t) + t := by
        rcases eq_or_lt_of_le ht with ht0 | ht0
        · rw [← ht0, sub_zero, mul_one, add_zero]
          exact lt_of_le_of_ne hs (fun hz => h.2 hz.symm ht0.symm)
        · exact add_pos_of_nonneg_of_pos (mul_nonneg hs (sub_nonneg.mpr ht1)) ht0
      let k := U.re * (t / (2 * V.re)) + (s / (2 * U.re)) * V.re
      have hk : 0 ≤ k := by dsimp [k]; positivity
      have hw : (U * V).im = y * k := by
        rw [Complex.mul_im, hUi, hVi]
        simp only [k, mul_div_assoc]
        ring
      rw [him, hw, show 2 * (U * V).re * (y * k) = y * (2 * (U * V).re * k) by ring] at him_sq
      have hp := mul_left_cancel₀ h.1 him_sq
      exact pos_of_mul_pos_left (show 0 < (U * V).re * (2 * k) by linarith) (by positivity)
  have he : conj (kernel r α) * kernel (1 - r) β = (U * V)⁻¹ := by
    simp [kernel, show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, Complex.cpow_neg, U, V, mul_comm]
  rw [he]
  exact inverse_re_pos hprod

/-- The complementary ratio in the Euler branch, with the original factor of i. -/
def tau (r : ℂ) : ℂ := Complex.I * slitPeriod (1 - r) / slitPeriod r

theorem tau_im_pos {r : ℂ} (hr : r ∈ doubleSlit) : 0 < (tau r).im := by
  let f := kernel r
  let g := kernel (1 - r)
  let F := ∫ θ in (0 : ℝ)..endpoint, f θ
  let G := ∫ θ in (0 : ℝ)..endpoint, g θ
  have hf : Continuous f := continuous_kernel hr.1
  have hg : Continuous g := continuous_kernel (complement_mem hr)
  have hconj : conj F = ∫ θ in (0 : ℝ)..endpoint, conj (f θ) :=
    (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
      (hf.intervalIntegrable 0 endpoint)).symm
  have hα (α : ℝ) : 0 < (conj (f α) * G).re := by
    dsimp only [G]
    have hfg : Continuous (fun β => conj (f α) * g β) := continuous_const.mul hg
    rw [← intervalIntegral.integral_const_mul, integral_re _ hfg]
    exact intervalIntegral.integral_pos endpoint_pos
      (Complex.continuous_re.comp (continuous_const.mul hg)).continuousOn
      (fun β _ => (kernel_pair_re_pos hr α β).le)
      ⟨0, ⟨le_rfl, endpoint_pos.le⟩, kernel_pair_re_pos hr α 0⟩
  have hc : Continuous (fun α => conj (f α) * G) :=
    (Complex.continuous_conj.comp hf).mul continuous_const
  have hpos : 0 < (conj F * G).re := by
    rw [hconj, ← intervalIntegral.integral_mul_const, integral_re _ hc]
    exact intervalIntegral.integral_pos endpoint_pos
      (Complex.continuous_re.comp hc).continuousOn (fun θ _ => (hα θ).le)
      ⟨0, ⟨le_rfl, endpoint_pos.le⟩, hα 0⟩
  let c : ℝ := 2 / Real.pi
  have hcpos : 0 < c := div_pos (by norm_num) Real.pi_pos
  have hFG : 0 < (slitPeriod (1 - r) * conj (slitPeriod r)).re := by
    change 0 < ((2 / (Real.pi : ℂ)) * G * conj ((2 / (Real.pi : ℂ)) * F)).re
    rw [show (2 / (Real.pi : ℂ)) = (c : ℂ) by simp [c], map_mul, Complex.conj_ofReal, show (c : ℂ) * G * ((c : ℂ) * conj F) =
      (c : ℂ) * ((c : ℂ) * (conj F * G)) by ring, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_pos hcpos (mul_pos hcpos hpos)
  rw [tau, mul_div_assoc, Complex.mul_im]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  rw [div_eq_mul_inv, Complex.inv_def, ← mul_assoc, Complex.re_mul_ofReal]
  exact mul_pos hFG (inv_pos.mpr (Complex.normSq_pos.mpr (slitPeriod_ne_zero hr.1)))


private lemma midpoint_mem : (1 / 2 : ℂ) ∈ doubleSlit := by
  exact ⟨(mem_slitDomain _).2 (Or.inl (by norm_num)),
    Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num))⟩

private lemma slitDomain_star : StarConvex ℝ (1 / 2 : ℂ) slitDomain := by
  intro z hz a b ha hb hab
  have hre : (a • (1 / 2 : ℂ) + b • z).re = a / 2 + b * z.re := by
    simp [div_eq_mul_inv]
  have him : (a • (1 / 2 : ℂ) + b • z).im = b * z.im := by
    simp [Complex.div_im]
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · exact (mem_slitDomain _).2 (Or.inl (by rw [hre, ← hb0]; linarith))
  · rcases (mem_slitDomain z).1 hz with hz | hz
    · exact (mem_slitDomain _).2 (Or.inl (by
        rw [hre]
        nlinarith [mul_lt_mul_of_pos_left hz hb0]))
    · exact (mem_slitDomain _).2 (Or.inr (by rw [him]; exact mul_ne_zero hb0.ne' hz))

private lemma doubleSlit_preconnected : IsPreconnected doubleSlit := by
  apply IsConnected.isPreconnected
  apply IsPathConnected.isConnected
  apply StarConvex.isPathConnected _ midpoint_mem
  intro z hz a b ha hb hab
  refine ⟨slitDomain_star hz.1 ha hb hab, Complex.mem_slitPlane_iff.2 ?_⟩
  have hre : (a • (1 / 2 : ℂ) + b • z).re = a / 2 + b * z.re := by
    simp [div_eq_mul_inv]
  have him : (a • (1 / 2 : ℂ) + b • z).im = b * z.im := by
    simp [Complex.div_im]
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · exact Or.inl (by rw [hre, ← hb0]; linarith)
  · rcases Complex.mem_slitPlane_iff.1 hz.2 with hz | hz
    · exact Or.inl (by rw [hre]; positivity)
    · exact Or.inr (by rw [him]; exact mul_ne_zero hb0.ne' hz)

private lemma one_sub_ne_zero {r : ℂ} (hr : r ∈ slitDomain) : 1 - r ≠ 0 :=
  Complex.slitPlane_ne_zero hr

private lemma inv_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z⁻¹ ∈ Complex.slitPlane := by
  have hn := Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero hz)
  rw [Complex.mem_slitPlane_iff, Complex.inv_re, Complex.inv_im]
  exact (Complex.mem_slitPlane_iff.1 hz).imp (fun h => div_pos h hn)
    (fun h => div_ne_zero (neg_ne_zero.mpr h) hn.ne')

theorem pfaff_mem_slitDomain {r : ℂ} (hr : r ∈ slitDomain) :
    r / (r - 1) ∈ slitDomain := by
  change 1 - r / (r - 1) ∈ Complex.slitPlane
  have hz := one_sub_ne_zero hr
  have hd : r - 1 ≠ 0 := by simpa [neg_sub] using neg_ne_zero.mpr hz
  rw [show 1 - r / (r - 1) = (1 - r)⁻¹ by field_simp [hd, hz]; ring]
  exact inv_mem_slitPlane hr

private lemma pfaff_real {r : ℝ} (hr : r < 1) :
    slitPeriod ((r : ℂ) / ((r : ℂ) - 1)) =
      (1 - (r : ℂ)) ^ (1 / 2 : ℂ) * slitPeriod (r : ℂ) := by
  let q := r / (r - 1)
  have hr1 : 0 < 1 - r := sub_pos.mpr hr
  have hr0 : r - 1 ≠ 0 := sub_ne_zero.mpr hr.ne
  have hq : q < 1 := by
    change r / (r - 1) < 1
    exact (div_lt_iff_of_neg (sub_neg.mpr hr)).2 (by linarith)
  have hroot : (1 - (r : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (1 - r) : ℂ) := by
    rw [show 1 - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; rfl,
      Real.sqrt_eq_rpow, Complex.ofReal_cpow hr1.le]
    norm_num
  have hkernel (θ : ℝ) : kernel (q : ℂ) (endpoint - θ) =
      (Real.sqrt (1 - r) : ℂ) * kernel (r : ℂ) θ := by
    rw [real_kernel hq, real_kernel hr, ← Complex.ofReal_mul, Complex.ofReal_inj]
    rw [endpoint, Real.sin_pi_div_two_sub]
    have he : 1 - q * Real.cos θ ^ 2 =
        (1 - r * Real.sin θ ^ 2) / (1 - r) := by
      have htrig := Real.sin_sq_add_cos_sq θ
      rw [show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by linarith]
      dsimp [q]
      field_simp [hr0, hr1.ne']
      ring
    rw [he, Real.sqrt_div]
    · have hn : Real.sqrt (1 - r * Real.sin θ ^ 2) ≠ 0 := by
        apply ne_of_gt
        apply Real.sqrt_pos.2
        rcases le_or_gt r 0 with hr' | hr'
        · have := mul_nonpos_of_nonpos_of_nonneg hr' (sq_nonneg (Real.sin θ))
          linarith
        · have := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one θ) hr'.le
          linarith
      field_simp [hn, (Real.sqrt_pos.2 hr1).ne']
    · rcases le_or_gt r 0 with hr' | hr'
      · have := mul_nonpos_of_nonpos_of_nonneg hr' (sq_nonneg (Real.sin θ))
        linarith
      · have := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one θ) hr'.le
        linarith
  have href := intervalIntegral.integral_comp_sub_left (kernel (q : ℂ))
    (a := (0 : ℝ)) (b := endpoint) endpoint
  simp_rw [sub_self, sub_zero, hkernel, intervalIntegral.integral_const_mul] at href
  rw [hroot, show (r : ℂ) / ((r : ℂ) - 1) = (q : ℂ) by simp [q] ]
  change (2 / (Real.pi : ℂ)) * (∫ θ in (0 : ℝ)..endpoint, kernel (q : ℂ) θ) =
    (Real.sqrt (1 - r) : ℂ) * ((2 / (Real.pi : ℂ)) *
      ∫ θ in (0 : ℝ)..endpoint, kernel (r : ℂ) θ)
  rw [← href]
  ring

/-- Pfaff's transformation on the full slit domain, with the principal square root. -/
theorem pfaff {r : ℂ} (hr : r ∈ slitDomain) :
    slitPeriod (r / (r - 1)) = (1 - r) ^ (1 / 2 : ℂ) * slitPeriod r := by
  have hA : AnalyticOnNhd ℂ (fun z => slitPeriod (z / (z - 1))) slitDomain := by
    intro z hz
    have hz' : z - 1 ≠ 0 := by simpa [neg_sub] using neg_ne_zero.mpr (one_sub_ne_zero hz)
    have hq : AnalyticAt ℂ (fun w : ℂ => w / (w - 1)) z :=
      analyticAt_id.div (analyticAt_id.sub analyticAt_const) hz'
    exact AnalyticAt.comp (g := slitPeriod) (f := fun w : ℂ => w / (w - 1))
      (slitPeriod_analyticOnNhd _ (pfaff_mem_slitDomain hz)) hq
  have hB : AnalyticOnNhd ℂ (fun z => (1 - z) ^ (1 / 2 : ℂ) * slitPeriod z) slitDomain := by
    intro z hz
    exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hz).mul
      (slitPeriod_analyticOnNhd z hz)
  have hzero : (0 : ℂ) ∈ slitDomain := (mem_slitDomain _).2 (Or.inl (by norm_num))
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0,
      slitPeriod (z / (z - 1)) = (1 - z) ^ (1 / 2 : ℂ) * slitPeriod z := by
    simpa using frequently_ofReal_near 0 (p := fun z =>
      slitPeriod (z / (z - 1)) = (1 - z) ^ (1 / 2 : ℂ) * slitPeriod z)
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
        |>.mono fun _ ht => pfaff_real ht)
  exact hA.eqOn_of_preconnected_of_frequently_eq hB
    (slitDomain_star.isPathConnected midpoint_mem.1).isConnected.isPreconnected hzero hfreq hr

private lemma deriv_eq_period {r : ℂ} (hr : ‖r‖ < 1) :
    deriv slitPeriod r = deriv period r := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Metric.isOpen_ball.mem_nhds
    (show r ∈ Metric.ball (0 : ℂ) 1 by simpa using hr)] with z hz
  exact slitPeriod_eq_period (by simpa using hz)

private def wronskian (z : ℂ) : ℂ :=
  z * (1 - z) * (deriv slitPeriod z * slitPeriod (1 - z) +
    slitPeriod z * deriv slitPeriod (1 - z))

/-- The actual slit periods preserve the original complementary Wronskian. -/
theorem slit_wronskian {r : ℂ} (hr : r ∈ doubleSlit) :
    r * (1 - r) * (deriv slitPeriod r * slitPeriod (1 - r) +
      slitPeriod r * deriv slitPeriod (1 - r)) = 1 / (Real.pi : ℂ) := by
  have ha : AnalyticOnNhd ℂ wronskian doubleSlit := by
    intro z hz
    have hZ : AnalyticAt ℂ (fun w : ℂ => 1 - w) z := analyticAt_const.sub analyticAt_id
    have hf := slitPeriod_analyticOnNhd z hz.1
    have hg := slitPeriod_analyticOnNhd (1 - z) (complement_mem hz)
    exact (analyticAt_id.mul hZ).mul ((hf.deriv.mul (hg.comp hZ)).add
      (hf.mul (hg.deriv.comp hZ)))
  have he : wronskian =ᶠ[𝓝 (1 / 2 : ℂ)] fun _ => 1 / (Real.pi : ℂ) := by
    have h₁ : ∀ᶠ z : ℂ in 𝓝 (1 / 2 : ℂ), ‖z‖ < 1 :=
      (continuous_norm.continuousAt (x := (1 / 2 : ℂ))).eventually_lt
        continuousAt_const (by norm_num)
    have h₂ : ∀ᶠ z : ℂ in 𝓝 (1 / 2 : ℂ), ‖1 - z‖ < 1 :=
      (continuous_norm.comp (continuous_const.sub continuous_id)).continuousAt.eventually_lt
        continuousAt_const (by norm_num)
    filter_upwards [h₁, h₂] with z hz hz'
    simpa only [wronskian, slitPeriod_eq_period hz, slitPeriod_eq_period hz',
      deriv_eq_period hz, deriv_eq_period hz'] using
      OriginalHalfBinomialWronskian.original_wronskian hz hz'
  exact ha.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    doubleSlit_preconnected midpoint_mem he hr

/-- The complementary ratio has its original exact quotient derivative on the double slit. -/
theorem tau_hasDerivAt {r : ℂ} (hr : r ∈ doubleSlit) :
    HasDerivAt tau (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * slitPeriod r ^ 2)) r := by
  have h₀ := Complex.slitPlane_ne_zero hr.2
  have h₁ := one_sub_ne_zero hr.1
  have hp := slitPeriod_ne_zero hr.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf := (slitPeriod_differentiableAt hr.1).hasDerivAt
  have hg := (slitPeriod_differentiableAt (complement_mem hr)).hasDerivAt.comp r
    ((hasDerivAt_id r).const_sub 1)
  have hw := slit_wronskian hr
  have hW : deriv slitPeriod r * slitPeriod (1 - r) +
      slitPeriod r * deriv slitPeriod (1 - r) = 1 / ((Real.pi : ℂ) * r * (1 - r)) := by
    apply (eq_div_iff (by exact mul_ne_zero (mul_ne_zero hπ h₀) h₁)).2
    calc
      _ = (Real.pi : ℂ) * (r * (1 - r) *
          (deriv slitPeriod r * slitPeriod (1 - r) +
          slitPeriod r * deriv slitPeriod (1 - r))) := by ring
      _ = 1 := by rw [hw]; field_simp
  convert (hg.const_mul Complex.I).div hf hp using 1
  · rfl
  · change _ = (Complex.I * (deriv slitPeriod (1 - r) * (-1)) * slitPeriod r -
      Complex.I * slitPeriod (1 - r) * deriv slitPeriod r) / slitPeriod r ^ 2
    calc
      _ = -Complex.I * (1 / ((Real.pi : ℂ) * r * (1 - r))) / slitPeriod r ^ 2 := by
        field_simp
      _ = _ := by rw [← hW]; ring

/-- A uniform strictly positive imaginary part on any compact subset of the double slit. -/
theorem exists_pos_le_tau_im {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ doubleSlit) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ (tau z).im := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, zero_lt_one, by simp [h]⟩
  have hc : ContinuousOn (fun z => (tau z).im) K :=
    Complex.continuous_im.comp_continuousOn fun z hz =>
      (tau_hasDerivAt (hsub hz)).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn h hc
  exact ⟨(tau z).im, tau_im_pos (hsub hz), fun w hw => hmin hw⟩

private lemma doubleSlit_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∈ doubleSlit :=
  ⟨(mem_slitDomain z).2 (Or.inr hz), Complex.mem_slitPlane_iff.2 (Or.inr hz)⟩

/-- The A, B and D chart parameters share a positive lower bound on compact
sets of nonreal cross-ratios. -/
theorem exists_pos_le_tau_im_charts {K : Set ℂ} (hK : IsCompact K)
    (hK_im : ∀ z ∈ K, z.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K,
      c ≤ (tau (1 - 1 / z)).im ∧ c ≤ (tau z).im ∧ c ≤ (tau (1 / z)).im := by
  let A := (fun z : ℂ => 1 - 1 / z) '' K
  let D := (fun z : ℂ => 1 / z) '' K
  have hne (z : ℂ) (hz : z ∈ K) : z ≠ 0 := by
    rintro rfl
    exact hK_im 0 hz Complex.zero_im
  have hD : ContinuousOn (fun z : ℂ => 1 / z) K :=
    continuousOn_const.div continuousOn_id hne
  have hA : ContinuousOn (fun z : ℂ => 1 - 1 / z) K := continuousOn_const.sub hD
  have hset : A ∪ K ∪ D ⊆ doubleSlit := by
    intro w hw
    have hi (z : ℂ) (hz : z ∈ K) : (1 / z).im ≠ 0 := by
      rw [one_div, Complex.inv_im]
      exact div_ne_zero (neg_ne_zero.mpr (hK_im z hz))
        (Complex.normSq_pos.mpr (hne z hz)).ne'
    apply doubleSlit_of_im_ne_zero
    rcases hw with (⟨z, hz, rfl⟩ | hw) | ⟨z, hz, rfl⟩
    · simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero] using hi z hz
    · exact hK_im w hw
    · exact hi z hz
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_tau_im
    (((hK.image_of_continuousOn hA).union hK).union (hK.image_of_continuousOn hD)) hset
  exact ⟨c, hc, fun z hz => ⟨hbound _ (Or.inl (Or.inl ⟨z, hz, rfl⟩)),
    hbound _ (Or.inl (Or.inr hz)), hbound _ (Or.inr ⟨z, hz, rfl⟩)⟩⟩

end D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
