/- GID: D5/S3/Fourier/SmoothConvolutionUniqueness
   generality: G
   mirror-B: D5/B/S3/Fourier/SmoothConvolutionUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancel integrable kernels with smooth nonvanishing Fourier transform against bounded measurable functions. -/

import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Tactic

/-!
All declarations concern unbounded analytic functions and Lebesgue integration.
They contain no finite enumeration, checker, numerical reduction, or certified finite instance.
Compact frequency division and L1 approximation yield cancellation without integrability
or continuity assumptions on the bounded function.
-/

namespace D5.S3.Fourier.SmoothConvolutionUniqueness

open MeasureTheory FourierTransform
open scoped SchwartzMap Convolution Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem compact_frequency_factor {k q : ℝ → ℂ}
    (hk : Integrable k) (hm : ContDiff ℝ ∞ (𝓕 k))
    (hn : ∀ x, 𝓕 k x ≠ 0) (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) :
    ∃ h : SchwartzMap ℝ ℂ, ∀ y : ℝ,
      (∫ u : ℝ, k u * h (y - u)) = 𝓕⁻ q y := by
  have hd : ContDiff ℝ ∞ (fun x => q x / 𝓕 k x) := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hq.mul (hm.inv hn)
  have hs : HasCompactSupport (fun x => q x / 𝓕 k x) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, zero_div]
  let s : SchwartzMap ℝ ℂ := hs.toSchwartzMap hd
  let h : SchwartzMap ℝ ℂ := 𝓕⁻ s
  have hh : 𝓕 (h : ℝ → ℂ) = fun x => q x / 𝓕 k x := by
    change 𝓕 (h : ℝ → ℂ) = (s : ℝ → ℂ)
    rw [← SchwartzMap.fourier_coe]
    change ((𝓕 (𝓕⁻ s) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = s
    rw [fourier_fourierInv_eq]
  have hft : 𝓕 (k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) = q := by
    ext x
    rw [Real.fourier_mul_convolution_eq hk h.integrable, hh]
    exact mul_div_cancel₀ (q x) (hn x)
  have hcont : Continuous (k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) := by
    apply BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) ?_ hk h.continuous
    exact ⟨SchwartzMap.seminorm ℝ 0 0 h,
      fun _ ⟨x, hx⟩ => hx ▸ SchwartzMap.norm_le_seminorm ℝ h x⟩
  have hint : Integrable (k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) :=
    hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) h.integrable
  have hinv := hcont.fourierInv_fourier_eq hint
    (hft ▸ hq.continuous.integrable_of_hasCompactSupport hc)
  refine ⟨h, fun y => ?_⟩
  change (k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) y = 𝓕⁻ q y
  rw [← hinv, hft]


private theorem bounded_convolution_factor_annihilation {k h g : ℝ → ℂ}
    (hk : Integrable k) (hh : Integrable h)
    (hg : AEStronglyMeasurable g volume) {M : ℝ}
    (_hM : 0 ≤ M) (hb : ∀ x, ‖g x‖ ≤ M)
    (hz : ∀ y, ∫ u : ℝ, k u * g (y - u) = 0) :
    ∀ y : ℝ, ∫ u : ℝ, (∫ v : ℝ, k v * h (u - v)) * g (y - u) = 0 := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hkg (y : ℝ) : ConvolutionExistsAt k g y B volume := by
    refine (hk.norm.mul_const M).mono'
      (hk.aestronglyMeasurable.convolution_integrand_snd B hg y) ?_
    filter_upwards with u
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
  intro y
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => g (y - p.1))
      (volume.prod volume) :=
    (hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume y)).comp_fst
  have hbase : Integrable (fun p : ℝ × ℝ => h p.2 * k (p.1 - p.2))
      (volume.prod volume) := hh.convolution_integrand B hk
  have hi : Integrable (Function.uncurry fun x v =>
      B (h v) (B (k (x - v)) (g (y - x)))) (volume.prod volume) := by
    have hmajor := (hh.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      hk.norm).mul_const M
    refine hmajor.mono' ?_ ?_
    · convert hbase.aestronglyMeasurable.mul hgm using 1
      ext p
      exact (mul_assoc _ _ _).symm
    · filter_upwards with p
      change ‖h p.2 * (k (p.1 - p.2) * g (y - p.1))‖ ≤
        (‖h p.2‖ * ‖k (p.1 - p.2)‖) * M
      simp only [norm_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have ha := convolution_assoc' B B B B (fun x v z => mul_assoc x v z) 
    (hh.ae_convolution_exists B hk) (Filter.Eventually.of_forall hkg) hi
  have hzero : (k ⋆[B] g) = 0 := funext hz
  have hcomm : (h ⋆[B] k) = (k ⋆[B] h) := by
    rw [← convolution_flip]
    have hB : B.flip = B := by
      ext
      exact mul_comm _ _
    rw [hB]
  change ((k ⋆[B] h) ⋆[B] g) y = 0
  rw [← hcomm, ha, hzero, convolution_zero]
  rfl

private theorem l1_translation_continuity {f : ℝ → ℂ} (hf : Integrable f) :
    Filter.Tendsto (fun t : ℝ => ∫ x : ℝ, ‖f (x - t) - f x‖)
      (nhds 0) (nhds 0) := by
  let T : ℝ → C(ℝ, ℝ) := fun t => ⟨fun x => x - t, by fun_prop⟩
  have hT : Continuous T := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × ℝ => p.2 - p.1)
    fun_prop
  have hmp (t : ℝ) : MeasurePreserving (T t) volume volume :=
    measurePreserving_sub_right volume t
  let F : ℝ → Lp ℂ 1 volume := fun t =>
    Lp.compMeasurePreserving (T t) (hmp t) (hf.toL1 f)
  have hF : Continuous F := continuous_const.compMeasurePreservingLp hT hmp (by simp)
  have hFe (t : ℝ) : (F t : ℝ → ℂ) =ᵐ[volume] (fun x => f (x - t)) := by
    exact (Lp.coeFn_compMeasurePreserving (hf.toL1 f) (hmp t)).trans
      ((hmp t).quasiMeasurePreserving.ae hf.coeFn_toL1)
  have he (t : ℝ) : ‖F t - F 0‖ = ∫ x : ℝ, ‖f (x - t) - f x‖ := by
    have hm : AEStronglyMeasurable (fun x => f (x - t) - f x) volume :=
      ((hf.comp_sub_right t).sub hf).aestronglyMeasurable
    rw [L1.norm_sub_eq_lintegral, integral_norm_eq_lintegral_enorm hm]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hFe t, hFe 0] with x hx h0
    simp only [hx, h0, sub_zero]
  have hlim := (hF.sub (continuous_const (y := F 0))).norm.tendsto 0
  simpa only [Pi.sub_apply, he, sub_self, norm_zero] using hlim


private theorem l1_translation_bound {f : ℝ → ℂ} (hf : Integrable f) (t : ℝ) :
    (∫ x : ℝ, ‖f (x - t) - f x‖) ≤ 2 * ∫ x : ℝ, ‖f x‖ := by
  calc
    _ ≤ ∫ x : ℝ, (‖f (x - t)‖ + ‖f x‖) :=
      integral_mono ((hf.comp_sub_right t).sub hf).norm
        ((hf.comp_sub_right t).norm.add hf.norm) (fun x => norm_sub_le _ _)
    _ = _ := by
      rw [integral_add (hf.comp_sub_right t).norm hf.norm,
        integral_sub_right_eq_self (fun x => ‖f x‖) t]
      ring

private theorem weighted_translation_limit {p f : ℝ → ℂ}
    (hp : Integrable p) (hf : Integrable f) (hc : Continuous f) :
    Filter.Tendsto (fun t : ℝ => ∫ v : ℝ, ‖p v‖ *
      (∫ x : ℝ, ‖f (x - t * v) - f x‖)) (nhds 0) (nhds 0) := by
  have hm (t : ℝ) : AEStronglyMeasurable
      (fun v : ℝ => ‖p v‖ * ∫ x : ℝ, ‖f (x - t * v) - f x‖) volume := by
    have hm' : AEStronglyMeasurable
        (fun z : ℝ × ℝ => ‖f (z.2 - t * z.1) - f z.2‖) (volume.prod volume) :=
      (by fun_prop : Continuous _).aestronglyMeasurable
    exact hp.aestronglyMeasurable.norm.mul hm'.integral_prod_right'
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (l := nhds (0 : ℝ))
    (F := fun t v : ℝ => ‖p v‖ * ∫ x : ℝ, ‖f (x - t * v) - f x‖)
    (f := fun _ : ℝ => (0 : ℝ))
    (fun v : ℝ => 2 * (∫ x : ℝ, ‖f x‖) * ‖p v‖)
    (Filter.Eventually.of_forall hm) ?_ (hp.norm.const_mul _) ?_
  · simpa only [integral_zero] using hlim
  · filter_upwards with t
    filter_upwards with v
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _))]
    calc
      _ ≤ ‖p v‖ * (2 * ∫ x : ℝ, ‖f x‖) :=
        mul_le_mul_of_nonneg_left (l1_translation_bound hf _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · filter_upwards with v
    have ht : Filter.Tendsto (fun t : ℝ => t * v) (nhds 0) (nhds 0) := by
      simpa only [zero_mul] using (continuous_mul_const v).tendsto (0 : ℝ)
    simpa using ((l1_translation_continuity hf).comp ht).const_mul ‖p v‖


private theorem approximation_error (p f : SchwartzMap ℝ ℂ)
    (hp : ∫ v : ℝ, p v = 1) (t : ℝ) :
    Integrable (fun x : ℝ => (∫ v : ℝ, p v * f (x - t * v)) - f x) ∧
    (∫ x : ℝ, ‖(∫ v : ℝ, p v * f (x - t * v)) - f x‖) ≤
      ∫ v : ℝ, ‖p v‖ * (∫ x : ℝ, ‖f (x - t * v) - f x‖) := by
  let D : ℝ × ℝ → ℂ := fun z => p z.1 * (f (z.2 - t * z.1) - f z.2)
  have hDc : Continuous D := by dsimp [D]; fun_prop
  have hDi : Integrable D (volume.prod volume) := by
    rw [integrable_prod_iff hDc.aestronglyMeasurable]
    constructor
    · filter_upwards with v
      exact ((f.integrable.comp_sub_right (t * v)).sub f.integrable).const_mul (p v)
    · refine (p.integrable.norm.mul_const (2 * ∫ x : ℝ, ‖f x‖)).mono'
        hDc.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards with v
      change ‖∫ x : ℝ, ‖p v * (f (x - t * v) - f x)‖‖ ≤ _
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp_rw [norm_mul, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (l1_translation_bound f.integrable _) (norm_nonneg _)
  have he (x : ℝ) : (∫ v : ℝ, p v * f (x - t * v)) - f x = ∫ v : ℝ, D (v, x) := by
    have hi : Integrable (fun v : ℝ => p v * f (x - t * v)) := by
      apply p.integrable.mul_bdd (by fun_prop)
      exact Filter.Eventually.of_forall fun v => SchwartzMap.norm_le_seminorm ℝ f _
    dsimp [D]
    simp_rw [mul_sub]
    rw [integral_sub hi (p.integrable.mul_const (f x)), integral_mul_const, hp, one_mul]
  refine ⟨?_, ?_⟩
  · simp_rw [he]
    exact hDi.integral_prod_right
  · simp_rw [he]
    calc
      _ ≤ ∫ x : ℝ, ∫ v : ℝ, ‖D (v, x)‖ :=
        integral_mono hDi.integral_prod_right.norm hDi.norm.integral_prod_right
          (fun x => norm_integral_le_integral_norm _)
      _ = ∫ v : ℝ, ∫ x : ℝ, ‖D (v, x)‖ := (integral_integral_swap hDi.norm).symm
      _ = _ := by simp only [D, norm_mul, integral_const_mul]


private theorem fourier_scale (p : ℝ → ℂ) {t : ℝ} (ht : 0 < t) (w : ℝ) :
    𝓕 (fun u : ℝ => (t⁻¹ : ℂ) * p (u / t)) w = 𝓕 p (t * w) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have he (u : ℝ) : -2 * Real.pi * (u / t) * (t * w) = -2 * Real.pi * u * w := by
    field_simp
  calc
    _ = (t⁻¹ : ℂ) * ∫ u : ℝ,
        (fun v : ℝ => Complex.exp ((↑(-2 * Real.pi * v * (t * w)) : ℂ) * Complex.I) * p v)
          (u / t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      simp only [he]
      ring
    _ = _ := by
      rw [Measure.integral_comp_div (fun v : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * v * (t * w)) : ℂ) * Complex.I) * p v) t,
        abs_of_pos ht, Complex.real_smul]
      rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'), one_mul]

private theorem scaled_convolution (p f : ℝ → ℂ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ u : ℝ, ((t⁻¹ : ℂ) * p (u / t)) * f (x - u)) =
      ∫ v : ℝ, p v * f (x - t * v) := by
  calc
    _ = (t⁻¹ : ℂ) * ∫ u : ℝ, (fun v : ℝ => p v * f (x - t * v)) (u / t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      rw [mul_div_cancel₀ _ ht.ne']
      ring
    _ = _ := by
      rw [Measure.integral_comp_div (fun v : ℝ => p v * f (x - t * v)) t,
        abs_of_pos ht, Complex.real_smul]
      rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'), one_mul]


private theorem compact_frequency_test_approximation {phi : ℝ → ℂ}
    (hphi : ContDiff ℝ ∞ phi) (hsphi : HasCompactSupport phi)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ q : ℝ → ℂ, ContDiff ℝ ∞ q ∧ HasCompactSupport q ∧
      Integrable (fun x => 𝓕⁻ q x - phi x) ∧
      (∫ x : ℝ, ‖𝓕⁻ q x - phi x‖) < eps := by
  let c : ContDiffBump (0 : ℝ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hbc : HasCompactSupport (fun x : ℝ => (c x : ℂ)) :=
    c.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let b : SchwartzMap ℝ ℂ := hbc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp c.contDiff)
  let p : SchwartzMap ℝ ℂ := 𝓕⁻ b
  let f : SchwartzMap ℝ ℂ := hsphi.toSchwartzMap hphi
  have hpft : 𝓕 (p : ℝ → ℂ) = b := by
    rw [← SchwartzMap.fourier_coe]
    change ((𝓕 (𝓕⁻ b) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = b
    rw [fourier_fourierInv_eq]
  have hp : ∫ v : ℝ, p v = 1 := by
    have hz : 𝓕 (p : ℝ → ℂ) 0 = ∫ v : ℝ, p v := by
      simp [Real.fourier_real_eq_integral_exp_smul]
    rw [← hz, hpft]
    change (c 0 : ℂ) = 1
    rw [c.one_of_mem_closedBall (by simp [c]), Complex.ofReal_one]
  have hl := (weighted_translation_limit p.integrable f.integrable f.continuous).mono_left
    (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
  obtain ⟨t, htE, ht⟩ := ((hl.eventually (gt_mem_nhds heps)).and self_mem_nhdsWithin).exists
  have htpos : 0 < t := ht
  let a : ℝ → ℂ := fun u => (t⁻¹ : ℂ) * p (u / t)
  have hai : Integrable a :=
    ((integrable_comp_div_iff (p : ℝ → ℂ) htpos.ne').2 p.integrable).const_mul _
  let q : ℝ → ℂ := fun w => b (t * w) * 𝓕 (f : ℝ → ℂ) w
  have hqd : ContDiff ℝ ∞ q := by
    exact (b.smooth'.comp (contDiff_const.mul contDiff_id)).mul (𝓕 f).smooth'
  have hqc : HasCompactSupport q := by
    have hb : HasCompactSupport (b : ℝ → ℂ) := hbc
    have hbt := hb.comp_homeomorph (Homeomorph.mulLeft₀ t htpos.ne')
    rw [hasCompactSupport_iff_eventuallyEq] at hbt ⊢
    filter_upwards [hbt] with w hw
    change b (t * w) = 0 at hw
    change b (t * w) * 𝓕 (f : ℝ → ℂ) w = 0
    rw [hw, zero_mul]
  have hft : 𝓕 (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) = q := by
    ext w
    rw [Real.fourier_mul_convolution_eq hai f.integrable]
    change 𝓕 (fun u : ℝ => (t⁻¹ : ℂ) * p (u / t)) w * _ = _
    rw [fourier_scale _ htpos, hpft]
  have hcont : Continuous (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) := by
    apply BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) ?_ hai f.continuous
    exact ⟨SchwartzMap.seminorm ℝ 0 0 f,
      fun _ ⟨x, hx⟩ => hx ▸ SchwartzMap.norm_le_seminorm ℝ f x⟩
  have hi := hai.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) f.integrable
  have hinv := hcont.fourierInv_fourier_eq hi
    (hft ▸ hqd.continuous.integrable_of_hasCompactSupport hqc)
  have he (x : ℝ) : 𝓕⁻ q x = ∫ v : ℝ, p v * f (x - t * v) := by
    rw [← hft, hinv]
    exact scaled_convolution p f htpos x
  refine ⟨q, hqd, hqc, ?_, ?_⟩
  · change Integrable (fun x => 𝓕⁻ q x - f x)
    simpa only [he] using (approximation_error p f hp t).1
  · change (∫ x : ℝ, ‖𝓕⁻ q x - f x‖) < eps
    simpa only [he] using (approximation_error p f hp t).2.trans_lt htE


private theorem bounded_pairing_separation {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, ‖g x‖ ≤ M)
    (hz : ∀ q : ℝ → ℂ, ContDiff ℝ ∞ q → HasCompactSupport q →
      ∫ u : ℝ, 𝓕⁻ q u * g (-u) = 0) : ∀ᵐ x ∂volume, g x = 0 := by
  have hgm : AEStronglyMeasurable (fun u => g (-u)) volume :=
    hg.comp_quasiMeasurePreserving (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  have hpair {a : ℝ → ℂ} (ha : Integrable a) : Integrable (fun u => a u * g (-u)) :=
    ha.mul_bdd hgm (Filter.Eventually.of_forall fun u => hb (-u))
  have hbound {a : ℝ → ℂ} (ha : Integrable a) :
      ‖∫ u : ℝ, a u * g (-u)‖ ≤ (M + 1) * ∫ u : ℝ, ‖a u‖ := by
    calc
      _ ≤ ∫ u : ℝ, ‖a u * g (-u)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ, (M + 1) * ‖a u‖ :=
        integral_mono (hpair ha).norm (ha.norm.const_mul _) (fun u => by
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right ((hb _).trans (by linarith)) (norm_nonneg _))
      _ = _ := integral_const_mul _ _
  have hall (phi : ℝ → ℂ) (hd : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
      ∫ u : ℝ, phi u * g (-u) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro eps heps
    obtain ⟨q, hqd, hqc, hdi, hde⟩ := compact_frequency_test_approximation hd hc
      (div_pos heps (by linarith : 0 < M + 1))
    have hphii : Integrable phi volume := hd.continuous.integrable_of_hasCompactSupport hc
    have hqi : Integrable (𝓕⁻ q) := by
      apply (hdi.add hphii).congr
      filter_upwards with u
      exact sub_add_cancel _ _
    have he : (∫ u : ℝ, (𝓕⁻ q u - phi u) * g (-u)) =
        -(∫ u : ℝ, phi u * g (-u)) := by
      simp_rw [sub_mul]
      rw [integral_sub (hpair hqi) (hpair hphii), hz q hqd hqc, zero_sub]
    have hnorm := hbound hdi
    rw [he, norm_neg] at hnorm
    have hlt : (M + 1) * (∫ u : ℝ, ‖𝓕⁻ q u - phi u‖) < eps := by
      calc
        _ < (M + 1) * (eps / (M + 1)) := mul_lt_mul_of_pos_left hde (by linarith)
        _ = eps := mul_div_cancel₀ _ (by linarith : M + 1 ≠ 0)
    simpa only [zero_add] using (hnorm.trans_lt hlt).le
  have hloc : LocallyIntegrable g volume :=
    (locallyIntegrable_const M).mono hg (Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_of_nonneg hM] using hb u)
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
  intro r hrd hrc
  have hrd' : ContDiff ℝ ∞ (fun u : ℝ => (r (-u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hrd.comp contDiff_neg)
  have hrc' : HasCompactSupport (fun u : ℝ => (r (-u) : ℂ)) :=
    (hrc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := Complex.ofReal) (by simp)
  have hr := hall _ hrd' hrc'
  have he := integral_neg_eq_self (fun u : ℝ => (r u : ℂ) * g u)
  simpa only [← he, Complex.real_smul] using hr

/-- An integrable kernel with smooth nowhere-zero Fourier transform cancels against
any AE strongly measurable, pointwise bounded complex function on the real line. -/
theorem ae_eq_zero_of_smooth_fourier_convolution_eq_zero
    {k g : ℝ → ℂ} (hk : Integrable k volume)
    (hm : ContDiff ℝ ∞ (𝓕 k)) (hn : ∀ xi : ℝ, 𝓕 k xi ≠ 0)
    (hg : AEStronglyMeasurable g volume)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, ‖g y‖ ≤ M)
    (hz : ∀ y : ℝ, ∫ u : ℝ, k u * g (y - u) = 0) :
    ∀ᵐ y ∂volume, g y = 0 := by
  obtain ⟨M, hM, hbound⟩ := hb
  apply bounded_pairing_separation hg hM hbound
  intro q hqd hqc
  obtain ⟨h, hh⟩ := compact_frequency_factor hk hm hn hqd hqc
  have ha := bounded_convolution_factor_annihilation hk h.integrable hg hM hbound hz 0
  simpa only [hh, zero_sub] using ha


end D5.S3.Fourier.SmoothConvolutionUniqueness

