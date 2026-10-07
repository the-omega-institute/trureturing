/- GID: D5/S3/Fourier/Asymptotics/CosineCutoffKernel/Highpass
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineCutoffKernel/Highpass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual positive cosine-integral high-pass kernels are limits of the finite cutoff kernels in Lebesgue L2 and in the original Gaussian integral-operator norm. -/

import D5.S3.Fourier.Asymptotics.CosineCutoffKernel
import D5.S3.Fourier.Asymptotics.CosineIntegralGram
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
namespace D5.S3.Fourier.Asymptotics.CosineCutoffKernel
open CosineIntegralLattice (cosineIntegral)
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The positive-Ci high-pass kernel, with a totalized value at the null origin. -/
def highpassKernel (c x : ℝ) : ℝ := 2 * cosineIntegral (c * |x|)

private theorem ci_measurable : Measurable cosineIntegral := by
  let f : ℝ × ℝ → ℝ := fun z => if z.1 < z.2 then Real.sin z.2 / z.2^2 else 0
  have hm : Measurable f :=
    ((Real.measurable_sin.comp measurable_snd).div (measurable_snd.pow_const 2)).piecewise
      (measurableSet_lt measurable_fst measurable_snd) measurable_const
  have hi : Measurable (fun x : ℝ => ∫ t : ℝ, f (x,t)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun x : ℝ => ∫ t : ℝ, f (x,t)) =
      (fun x : ℝ => ∫ t in Ioi x, Real.sin t / t^2) := by
    funext x
    rw [← integral_indicator measurableSet_Ioi]
    rfl
  rw [he] at hi
  exact (Real.measurable_sin.div measurable_id).sub hi

private theorem highpass_memLp (c : ℝ) (hc : 0 < c) :
    Measurable (highpassKernel c) ∧ MemLp (highpassKernel c) 2 volume := by
  have hm : Measurable (fun x : ℝ => cosineIntegral (c*|x|)) :=
    ci_measurable.comp (measurable_const.mul continuous_abs.measurable)
  have hi := (CosineIntegralGram.result c c hc hc).1
  have h2 : MemLp (fun x : ℝ => cosineIntegral (c*|x|)) 2 volume :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr (by simpa [pow_two] using hi)
  exact ⟨measurable_const.mul hm, h2.const_mul 2⟩

private theorem cutoff_difference (c N : ℝ) (hc : 0 < c) (hN : c ≤ N) :
    kernel c N =ᵐ[volume] (fun x => highpassKernel c x - highpassKernel N x) := by
  let p : ℝ → ℝ := fun t => (Real.cos t-1)/t
  have hp (a b : ℝ) : IntervalIntegrable p volume a b := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
    · exact ((Real.measurable_cos.sub measurable_const).div measurable_id).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro t
      change ‖p t‖ ≤ 1
      rw [Real.norm_eq_abs]
      by_cases ht : t = 0
      · simp [p, ht]
      · have hb := Real.abs_cos_sub_cos_le t 0
        simp only [Real.cos_zero, sub_zero] at hb
        dsimp [p]
        rw [abs_div]
        exact (div_le_one (abs_pos.mpr ht)).mpr hb
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hxpos : 0 < |x| := abs_pos.mpr hx0
  have hNp : 0 < N := hc.trans_le hN
  have hca := CosineNormalizedRemainder.positive_normalization (c*|x|) (mul_pos hc hxpos)
  have hNa := CosineNormalizedRemainder.positive_normalization (N*|x|) (mul_pos hNp hxpos)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hp 0 (c*|x|))
    (hp (c*|x|) (N*|x|))
  have hsub : (∫ t in c*|x|..N*|x|, p t) = ∫ t in c..N, (Real.cos (t*x)-1)/t := by
    have hh := intervalIntegral.mul_integral_comp_mul_right
      (a:=c) (b:=N) (f:=p) |x|
    calc
      _ = |x| * ∫ t in c..N, p (t*|x|) := hh.symm
      _ = ∫ t in c..N, (Real.cos (t*x)-1)/t := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [p]
        have hcos : Real.cos (t*|x|) = Real.cos (t*x) := by
          rcases le_total 0 x with h | h
          · rw [abs_of_nonneg h]
          · rw [abs_of_nonpos h, mul_neg, Real.cos_neg]
        rw [hcos]
        field_simp [hxpos.ne']
  have hcint : IntervalIntegrable (fun t : ℝ => Real.cos (t*x)/t) volume c N := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : 0 < t := hc.trans_le ((show t ∈ Icc c N by simpa [uIcc_of_le hN] using ht).1)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hint : IntervalIntegrable (fun t : ℝ => 1/t) volume c N := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : 0 < t := hc.trans_le ((show t ∈ Icc c N by simpa [uIcc_of_le hN] using ht).1)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hcosint : (∫ t in c..N, (Real.cos (t*x)-1)/t) =
      (∫ t in c..N, Real.cos (t*x)/t) - Real.log (N/c) := by
    simp_rw [sub_div]
    rw [intervalIntegral.integral_sub hcint hint, integral_one_div_of_pos hc hNp]
  have hlog : Real.log (N*|x|)-Real.log (c*|x|) = Real.log (N/c) := by
    rw [Real.log_mul hNp.ne' hxpos.ne', Real.log_mul hc.ne' hxpos.ne',
      Real.log_div hNp.ne' hc.ne']
    ring
  dsimp [kernel, highpassKernel]
  rw [hca,hNa]
  change _ = 2*(Real.eulerMascheroniConstant+Real.log (c*|x|)+∫ t in 0..c*|x|, p t) -
    2*(Real.eulerMascheroniConstant+Real.log (N*|x|)+∫ t in 0..N*|x|, p t)
  rw [hsub,hcosint] at hsplit
  linarith

/-- Exact L2 cutoff error and convergence for every real cutoff filter. -/
theorem highpass_limit (c : ℝ) (hc : 0 < c) :
    Measurable (highpassKernel c) ∧ ∃ hq : MemLp (highpassKernel c) 2 volume,
      (∀ N : ℝ, c ≤ N → ∀ hNq : MemLp (kernel c N) 2 volume,
        ‖hNq.toLp (kernel c N)-hq.toLp (highpassKernel c)‖^2 = 4*Real.pi/N) ∧
      (∀ (ι : Type) (l : Filter ι) (Ns : ι → ℝ) (hNs : ∀ i, c ≤ Ns i)
        (hcuts : ∀ i, MemLp (kernel c (Ns i)) 2 volume),
        Tendsto Ns l atTop →
        Tendsto (fun i => (hcuts i).toLp (kernel c (Ns i))) l
          (nhds (hq.toLp (highpassKernel c)))) := by
  obtain ⟨hmq,hq⟩ := highpass_memLp c hc
  have herr (N : ℝ) (hN : c ≤ N) (hNq : MemLp (kernel c N) 2 volume) :
      ‖hNq.toLp (kernel c N)-hq.toLp (highpassKernel c)‖^2 = 4*Real.pi/N := by
    have hNp : 0 < N := hc.trans_le hN
    obtain ⟨hmN,hqN⟩ := highpass_memLp N hNp
    have he : hNq.toLp (kernel c N)-hq.toLp (highpassKernel c) =
        -(hqN.toLp (highpassKernel N)) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (hNq.toLp (kernel c N)) (hq.toLp (highpassKernel c)),
        hNq.coeFn_toLp, hq.coeFn_toLp, Lp.coeFn_neg (hqN.toLp (highpassKernel N)),
        hqN.coeFn_toLp, cutoff_difference c N hc hN] with x hs hn hq' hneg hN' hd
      simp only [hs,hneg,Pi.sub_apply,Pi.neg_apply,hn,hq',hN',hd]
      ring
    rw [he,norm_neg,← real_inner_self_eq_norm_sq,L2.inner_def]
    have ht : (fun x : ℝ => ⟪hqN.toLp (highpassKernel N) x,
        hqN.toLp (highpassKernel N) x⟫) =ᵐ[volume]
        (fun x => 4*(cosineIntegral (N*|x|)*cosineIntegral (N*|x|))) := by
      filter_upwards [hqN.coeFn_toLp] with x hx
      rw [hx]
      simp only [highpassKernel,Real.inner_apply]
      ring
    rw [integral_congr_ae ht,integral_const_mul,(CosineIntegralGram.result N N hNp hNp).2,
      max_self]
    ring
  refine ⟨hmq,hq,herr,?_⟩
  intro ι l Ns hNs hcuts hlim
  have hs : Tendsto (fun i => ‖(hcuts i).toLp (kernel c (Ns i))-
      hq.toLp (highpassKernel c)‖^2) l (nhds 0) := by
    simp_rw [herr _ (hNs _) (hcuts _)]
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.const_mul (4*Real.pi)).comp hlim
  have hn : Tendsto (fun i => ‖(hcuts i).toLp (kernel c (Ns i))-
      hq.toLp (highpassKernel c)‖) l (nhds 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- Ordinary high-pass convolution on the full complex L2 space. The operator
is the norm limit of the actual finite convolution operators, without an L1 premise. -/
theorem actual_highpass_convolution (c : ℝ) (hc : 0 < c) :
    ∃ C : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ (f : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ),
        Integrable (fun y => (highpassKernel c (x-y) : ℂ)*f y) volume) ∧
      (∀ f, (C f : ℝ → ℂ) =ᵐ[volume]
        (fun x => ∫ y, (highpassKernel c (x-y) : ℂ)*f y)) ∧
      ‖C‖ ≤ 2*Real.pi/c ∧
      ∃ Cr : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ),
        (∀ f, (Cr f : ℝ → ℝ) =ᵐ[volume]
          (fun x => ∫ y, highpassKernel c (x-y)*f y)) ∧
        ‖Cr‖ ≤ 2*Real.pi/c := by
  classical
  let HC := Lp ℂ 2 (volume : Measure ℝ)
  let N (n : ℕ) : ℝ := c+(n:ℝ)
  have hN (n : ℕ) : c ≤ N n := le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop
  have hFinite (n : ℕ) : ∃ C : HC →L[ℂ] HC,
      (∀ f, (C f : ℝ → ℂ) =ᵐ[volume]
        (fun x => ∫ y, (kernel c (N n) (x-y) : ℂ)*f y)) ∧
      ‖C‖ ≤ 2*Real.pi/c ∧
      ∀ M : ℝ, N n ≤ M → ∃ D : HC →L[ℂ] HC,
        (∀ f, (D f : ℝ → ℂ) =ᵐ[volume]
          (fun x => ∫ y, (kernel c M (x-y) : ℂ)*f y)) ∧
        ‖D-C‖ ≤ 2*Real.pi/N n := by
    obtain ⟨_,C,hi,he,hb,ht⟩ := actual_cutoff_convolution c (N n) hc (hN n)
    refine ⟨C,?_,hb,ht⟩
    intro f
    obtain ⟨_,_,hf,_,_⟩ := he f
    exact hf
  choose Cs hCs hCsbound hCstail using hFinite
  have hdiff (n m : ℕ) (hnm : n ≤ m) : ‖Cs m-Cs n‖ ≤ 2*Real.pi/N n := by
    obtain ⟨D,hD,hDn⟩ := hCstail n (N m) (by dsimp [N]; exact add_le_add le_rfl (Nat.cast_le.mpr hnm : (n:ℝ) ≤ (m:ℝ)))
    have he : D = Cs m := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      exact (hD f).trans (hCs m f).symm
    rwa [he] at hDn
  have hz : Tendsto (fun n => 2*Real.pi/N n) atTop (nhds 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.const_mul (2*Real.pi)).comp hNtop
  have hCau : CauchySeq Cs := cauchySeq_of_le_tendsto_0'
    (fun n => 2*Real.pi/N n) (fun n m hnm => by
      rw [dist_comm,dist_eq_norm]
      exact hdiff n m hnm) hz
  obtain ⟨C,hClim⟩ := cauchySeq_tendsto_of_complete hCau
  have hCn : ‖C‖ ≤ 2*Real.pi/c :=
    le_of_tendsto hClim.norm (Filter.Eventually.of_forall hCsbound)
  obtain ⟨hmq,hq,herr,hqlim⟩ := highpass_limit c hc
  have hcuts (n : ℕ) : MemLp (kernel c (N n)) 2 volume :=
    (actual_cutoff_real c (N n) hc (hN n)).2.1
  let J : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] HC :=
    Complex.ofRealCLM.compLpL 2 volume
  let Q : HC := J (hq.toLp (highpassKernel c))
  let Qs (n : ℕ) : HC := J ((hcuts n).toLp (kernel c (N n)))
  have hQ : (Q : ℝ → ℂ) =ᵐ[volume] (fun x => (highpassKernel c x : ℂ)) := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (hq.toLp (highpassKernel c)),
      hq.coeFn_toLp] with x hx hy
    simpa only [Q,J,hy,Complex.ofRealCLM_apply] using hx
  have hQs (n : ℕ) : (Qs n : ℝ → ℂ) =ᵐ[volume]
      (fun x => (kernel c (N n) x : ℂ)) := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL ((hcuts n).toLp (kernel c (N n))),
      (hcuts n).coeFn_toLp] with x hx hy
    simpa only [Qs,J,hy,Complex.ofRealCLM_apply] using hx
  have hQlim : Tendsto Qs atTop (nhds Q) :=
    J.continuous.continuousAt.tendsto.comp (hqlim ℕ atTop N hN hcuts hNtop)
  let R (x : ℝ) : HC →ₗᵢ[ℂ] HC :=
    Lp.compMeasurePreservingₗᵢ ℂ (fun y : ℝ => x-y) (volume.measurePreserving_sub_left x)
  have hrow (P : HC) (p : ℝ → ℂ) (hp : (P : ℝ → ℂ) =ᵐ[volume] p) (x : ℝ) :
      (R x P : ℝ → ℂ) =ᵐ[volume] (fun y => p (x-y)) :=
    (Lp.coeFn_compMeasurePreserving P (volume.measurePreserving_sub_left x)).trans
      (hp.comp_tendsto (volume.measurePreserving_sub_left x).quasiMeasurePreserving.tendsto_ae)
  have hInt (f : HC) (x : ℝ) :
      Integrable (fun y => (highpassKernel c (x-y) : ℂ)*f y) volume := by
    apply (product_integrable (Lp.memLp (R x Q)) (Lp.memLp f)).congr
    filter_upwards [hrow Q _ hQ x] with y hy
    rw [hy]
  have hpair (P : HC) (p : ℝ → ℂ) (hp : (P : ℝ → ℂ) =ᵐ[volume] p)
      (f : HC) (x : ℝ) :
      pair (R x P) f = ∫ y, p (x-y)*f y := by
    rw [pair_eq]
    apply integral_congr_ae
    filter_upwards [hrow P p hp x] with y hy
    rw [hy]
  have hPoint (f : HC) (x : ℝ) :
      Tendsto (fun n => ∫ y, (kernel c (N n) (x-y) : ℂ)*f y) atTop
        (nhds (∫ y, (highpassKernel c (x-y) : ℂ)*f y)) := by
    have hh := (pair.flip f).continuous.continuousAt.tendsto.comp
      ((R x).continuous.continuousAt.tendsto.comp hQlim)
    simpa only [Function.comp_def,ContinuousLinearMap.flip_apply,
      hpair Q _ hQ f x, hpair (Qs _) _ (hQs _) f x] using hh
  have hCraw (f : HC) : (C f : ℝ → ℂ) =ᵐ[volume]
      (fun x => ∫ y, (highpassKernel c (x-y) : ℂ)*f y) := by
    have hCf : Tendsto (fun n => Cs n f) atTop (nhds (C f)) :=
      (ContinuousLinearMap.apply ℂ HC f).continuous.continuousAt.tendsto.comp hClim
    obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hCf).exists_seq_tendsto_ae
    have hRaw : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, Cs n f x =
        ∫ y, (kernel c (N n) (x-y) : ℂ)*f y := ae_all_iff.mpr (fun n => hCs n f)
    filter_upwards [hae,hRaw] with x hx hraw
    apply tendsto_nhds_unique hx
    have hh := (hPoint f x).comp hns.tendsto_atTop
    simpa only [Function.comp_def,hraw] using hh
  let ReL : HC →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) := Complex.reCLM.compLpL 2 volume
  let Cr : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    ReL.comp ((C.restrictScalars ℝ).comp J)
  have hJ (f : Lp ℝ 2 (volume : Measure ℝ)) :
      (J f : ℝ → ℂ) =ᵐ[volume] (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.coeFn_compLpL f
  have hRe (f : HC) : (ReL f : ℝ → ℝ) =ᵐ[volume] (fun x => (f x).re) :=
    Complex.reCLM.coeFn_compLpL f
  have hCr (f : Lp ℝ 2 (volume : Measure ℝ)) :
      (Cr f : ℝ → ℝ) =ᵐ[volume] (fun x => ∫ y, highpassKernel c (x-y)*f y) := by
    filter_upwards [hRe (C (J f)),hCraw (J f)] with x hx hcx
    change (ReL (C (J f))) x = _
    rw [hx,hcx]
    change Complex.reCLM (∫ y, (highpassKernel c (x-y) : ℂ)*(J f) y) = _
    rw [← Complex.reCLM.integral_comp_comm (hInt (J f) x)]
    apply integral_congr_ae
    filter_upwards [hJ f] with y hy
    simp [hy]
  have hCrn : ‖Cr‖ ≤ ‖C‖ := by
    apply Cr.opNorm_le_bound (norm_nonneg _)
    intro f
    have hre : ‖Cr f‖ ≤ ‖C (J f)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hRe (C (J f))] with x hx
      change ‖ReL (C (J f)) x‖ ≤ _
      rw [hx]
      exact Complex.abs_re_le_norm _
    have hjn : ‖J f‖ ≤ ‖f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hJ f] with x hx
      rw [hx]
      simp
    exact hre.trans ((C.le_opNorm (J f)).trans
      (mul_le_mul_of_nonneg_left hjn (norm_nonneg _)))
  exact ⟨C,hInt,hCraw,hCn,Cr,hCr,hCrn.trans hCn⟩

set_option maxHeartbeats 1200000 in
/-- The original Gaussian integral operator for the actual positive-Ci kernel.
Elaboration connects the expanded Gaussian coefficients across three operator interfaces. -/
theorem actual_highpass_operator (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let a : ℝ := (1+r)/2
    let b : ℝ := (1-r)/2
    let c0 : ℝ := 1/(4*Real.pi*Real.sqrt (a*b))
    let κ : ℝ := 1/a+α^2/b
    let ρ : ℝ → ℝ := fun x => c0*Real.exp (-κ*x^2/2)
    let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
    ∃ A : Lp ℝ 2 (μ.prod μ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ),
      (∀ K f, (A K f : ℝ → ℝ) =ᵐ[μ]
        (fun x => ∫ y, K (x,y)*f y ∂μ)) ∧
      ∀ c : ℝ, 0 < c →
      ∃ (C : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ))
        (K : Lp ℝ 2 (μ.prod μ)),
        (∀ f, (C f : ℝ → ℝ) =ᵐ[volume]
          (fun x => ∫ y, highpassKernel c (x-y)*f y)) ∧
        ‖C‖ ≤ 2*Real.pi/c ∧
        (K : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => highpassKernel c (z.1-z.2)) ∧
        (∀ f : Lp ℝ 2 μ, (A K f : ℝ → ℝ) =ᵐ[μ]
          (fun x => ∫ y, highpassKernel c (x-y)*f y ∂μ)) ∧
        (∀ f : Lp ℝ 2 μ, ∀ᵐ x ∂μ,
          Integrable (fun y => highpassKernel c (x-y)*f y) μ) ∧
        ‖A K‖ ≤ c0*(2*Real.pi/c) ∧
        (∃ (U : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ))
          (M : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ)),
          (∀ f, (U f : ℝ → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x)*f x)) ∧
          (∀ h, (U.symm h : ℝ → ℝ) =ᵐ[μ] (fun x => h x/Real.sqrt (ρ x))) ∧
          (∀ h, (M h : ℝ → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x)*h x)) ∧
          ‖M‖ ≤ Real.sqrt c0 ∧
          U.toLinearIsometry.toContinuousLinearMap.comp
            ((A K).comp U.symm.toLinearIsometry.toContinuousLinearMap) = M.comp (C.comp M)) ∧
        ∃ Ks : (N : ℝ) → c ≤ N → Lp ℝ 2 (μ.prod μ),
          (∀ N hN, (Ks N hN : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ]
            (fun z => kernel c N (z.1-z.2))) ∧
          (∀ N hN, ‖A (Ks N hN)‖ ≤ c0*(2*Real.pi/c)) ∧
          (∀ (ι : Type) (l : Filter ι) (Ns : ι → ℝ) (hNs : ∀ i, c ≤ Ns i),
            Tendsto Ns l atTop →
            Tendsto (fun i => Ks (Ns i) (hNs i)) l (nhds K) ∧
            Tendsto (fun i => A (Ks (Ns i) (hNs i))) l (nhds (A K))) := by
  classical
  let a : ℝ := (1+r)/2
  let b : ℝ := (1-r)/2
  let c0 : ℝ := 1/(4*Real.pi*Real.sqrt (a*b))
  let κ : ℝ := 1/a+α^2/b
  let ρ : ℝ → ℝ := fun x => c0*Real.exp (-κ*x^2/2)
  let μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  dsimp only
  obtain ⟨A,hA,hAn,hAlim,hAraw,hAclosed⟩ :=
    GaussianWeight.weighted_integral_operator r α hr0 hr1
  obtain ⟨hG,hg0,hBuild,hDiff,hLimit⟩ :=
    GaussianWeight.gaussian_weighted_kernel r α hr0 hr1
  refine ⟨A,hA,?_⟩
  intro c hc
  obtain ⟨hmq,hq,herr,hlim⟩ := highpass_limit c hc
  obtain ⟨K,hK,hKn,hKbound⟩ := hBuild (highpassKernel c) hmq hq
  have hcut (N : ℝ) (hN : c ≤ N) :
      Measurable (kernel c N) ∧ MemLp (kernel c N) 2 volume :=
    ⟨(actual_cutoff_real c N hc hN).1, (actual_cutoff_real c N hc hN).2.1⟩
  let Ks (N : ℝ) (hN : c ≤ N) : Lp ℝ 2 (μ.prod μ) :=
    (hBuild (kernel c N) (hcut N hN).1 (hcut N hN).2).choose
  have hKs (N : ℝ) (hN : c ≤ N) :
      (Ks N hN : ℝ × ℝ → ℝ) =ᵐ[μ.prod μ] (fun z => kernel c N (z.1-z.2)) :=
    (hBuild (kernel c N) (hcut N hN).1 (hcut N hN).2).choose_spec.1
  have hKsbound (N : ℝ) (hN : c ≤ N) : ‖A (Ks N hN)‖ ≤ c0*(2*Real.pi/c) := by
    obtain ⟨C,T,U,M,hC,hT,hTi,hU,hUinv,hM,hconj,hCn,hMn,hTn⟩ :=
      actual_weighted_cutoff r α hr0 hr1 c N hc hN
    have he : A (Ks N hN) = T := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      exact ((hAraw (Ks N hN) f (fun z => kernel c N (z.1-z.2)) f
        (hKs N hN).symm Filter.EventuallyEq.rfl).2.symm).trans (hT f).symm
    rw [he]
    exact hTn
  have hKslim (ι : Type) (l : Filter ι) (Ns : ι → ℝ) (hNs : ∀ i, c ≤ Ns i)
      (hNsTop : Tendsto Ns l atTop) :
      Tendsto (fun i => Ks (Ns i) (hNs i)) l (nhds K) :=
    hLimit ι l (fun i => kernel c (Ns i)) (highpassKernel c)
      (fun i => (hcut (Ns i) (hNs i)).1) hmq
      (fun i => (hcut (Ns i) (hNs i)).2) hq
      (fun i => Ks (Ns i) (hNs i)) K (fun i => hKs (Ns i) (hNs i)) hK
      (hlim ι l Ns hNs (fun i => (hcut (Ns i) (hNs i)).2) hNsTop)
  obtain ⟨Cc,hCci,hCc,hCcn,C,hC,hCn⟩ := actual_highpass_convolution c hc
  have hT (f : Lp ℝ 2 μ) : (A K f : ℝ → ℝ) =ᵐ[μ]
      (fun x => ∫ y, highpassKernel c (x-y)*f y ∂μ) :=
    (hAraw K f (fun z => highpassKernel c (z.1-z.2)) f hK.symm Filter.EventuallyEq.rfl).2.symm
  obtain ⟨U,hU,hUinv⟩ := GaussianWeight.density_unitary r α hr0 hr1
  obtain ⟨M,hM,hMn,hconj,hTn⟩ := GaussianWeight.cutoff_conjugacy r α hr0 hr1
    (highpassKernel c) hq C hC (A K) hT U hU hUinv
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hAK : ‖A K‖ ≤ c0*(2*Real.pi/c) :=
    hTn.trans (mul_le_mul_of_nonneg_left hCn hc0.le)
  refine ⟨C,K,hC,hCn,hK,hT,?_,hAK,⟨U,M,hU,hUinv,hM,hMn,hconj⟩,
    Ks,hKs,hKsbound,?_⟩
  · intro f
    exact (hAraw K f (fun z => highpassKernel c (z.1-z.2)) f hK.symm
      Filter.EventuallyEq.rfl).1
  · intro ι l Ns hNs hNsTop
    have hh := hKslim ι l Ns hNs hNsTop
    exact ⟨hh,hAlim ι l _ K hh⟩

end D5.S3.Fourier.Asymptotics.CosineCutoffKernel
