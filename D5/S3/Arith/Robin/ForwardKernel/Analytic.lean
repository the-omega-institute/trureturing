/- GID: D5/S3/Arith/Robin/ForwardKernel/Analytic
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/Analytic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual inverse-coordinate remainder gives a holomorphic Chebyshev tail. -/

import D5.S3.Arith.Robin.ForwardKernel.Asymptotic
import D5.S3.Arith.Robin.ForwardKernel.RemainderContinuation
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace D5.S3.Arith.Robin.ForwardKernel.Analytic

open Set MeasureTheory Filter
open scoped Topology
open ForwardKernel.Remainder ForwardKernel.Asymptotic ForwardKernel.WeightControl
open ActualVonMangoldtBandCompensation (discrepancy)

noncomputable section

private lemma parameter_derivative_measurable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℂ → α → ℂ}
    (hm : ∀ s, AEStronglyMeasurable (f s) μ)
    (hd : ∀ᵐ a ∂μ, Differentiable ℂ (fun s => f s a)) (s : ℂ) :
    AEStronglyMeasurable (fun a => deriv (fun z => f z a) s) μ := by
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hp : ∀ n, 0 < h n := fun n => by dsimp [h]; positivity
  have hseq : Tendsto (fun n => (h n : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [h, Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
          tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Eventually.of_forall (fun n => by
        simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using
          (hp n).ne')
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n a => (h n : ℂ)⁻¹ • (f (s + h n) a - f s a))
  · intro n
    exact ((hm (s + h n)).sub (hm s)).const_smul ((h n : ℂ)⁻¹)
  · filter_upwards [hd] with a ha
    exact ((ha s).hasDerivAt.tendsto_slope_zero).comp hseq

/-- A separately measurable entire family with compact uniform bounds has an entire integral. -/
lemma entire_integral_of_compact_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℂ → α → ℂ}
    (hm : ∀ s, AEStronglyMeasurable (f s) μ)
    (hd : ∀ᵐ a ∂μ, Differentiable ℂ (fun s => f s a))
    (hb : ∀ K : Set ℂ, IsCompact K →
      ∃ C : ℝ, ∀ᵐ a ∂μ, ∀ s ∈ K, ‖f s a‖ ≤ C) :
    Differentiable ℂ (fun s => ∫ a, f s a ∂μ) := by
  intro s
  let K : Set ℂ := Metric.closedBall s 2
  obtain ⟨C, hC⟩ := hb K (isCompact_closedBall _ _)
  have hsmem : s ∈ K := Metric.mem_closedBall_self (by norm_num)
  have hi : Integrable (f s) μ :=
    (integrable_const C).mono' (hm s) (hC.mono fun a ha => ha s hsmem)
  have hdk : ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball s 1, ‖deriv (fun z => f z a) y‖ ≤ C := by
    filter_upwards [hd, hC] with a ha hCa y hy
    have hsphere : ∀ z ∈ Metric.sphere y 1, z ∈ K := by
      intro z hz
      change dist z s ≤ 2
      have hz' : dist z y = 1 := hz
      have hy' : dist y s < 1 := hy
      calc
        dist z s ≤ dist z y + dist y s := dist_triangle _ _ _
        _ ≤ 2 := by linarith
    simpa only [div_one] using
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1)
        ha.diffContOnCl (fun z hz => hCa z (hsphere z hz))
  have hdiff : ∀ᵐ a ∂μ, ∀ y ∈ Metric.ball s 1,
      HasDerivAt (fun z => f z a) (deriv (fun z => f z a) y) y :=
    hd.mono fun a ha y _ => (ha y).hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := fun y a => deriv (fun z => f z a) y) (bound := fun _ => C)
    (Metric.ball_mem_nhds s (by norm_num)) (Eventually.of_forall hm) hi
    (parameter_derivative_measurable hm hd s) hdk (integrable_const C) hdiff).2.differentiableAt

private lemma kernelConstant_bounded (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, kernelConstant s ≤ C := by
  have hc : Continuous kernelConstant := by unfold kernelConstant; fun_prop
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc.continuousOn
  exact ⟨max 0 M, le_max_left _ _, fun s hs =>
    (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)⟩

private lemma finite_square : IsFiniteMeasure (volume.restrict unitSquare) := by
  constructor
  have h : volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  simpa only [Measure.restrict_apply_univ, unitSquare] using h

private lemma integrand_entire (t : ℝ) (p : ℝ × ℝ) :
    Differentiable ℂ (fun s => normalizedIntegrand t s p) := by
  by_cases hp : p ∈ triangle
  · simp only [normalizedIntegrand, indicator_of_mem hp, normalizedBody, normalizedPower]
    fun_prop
  · simp only [normalizedIntegrand, indicator_of_notMem hp]
    exact differentiable_const _

private lemma integrand_compact_bound {t : ℝ} (ht : 8 ≤ t)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ᵐ p ∂volume.restrict unitSquare, ∀ s ∈ K,
      ‖normalizedIntegrand t s p‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := kernelConstant_bounded K hK
  refine ⟨C + 1, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp s hs
  by_cases hpt : p ∈ triangle
  · rw [normalizedIntegrand, indicator_of_mem hpt]
    have he := (normalizedBody_C1_estimate ht hp.1 hp.2 s).2.1
    have hε : t ^ (-1 / 5 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : 1 ≤ t)
        (show (-1 / 5 : ℝ) ≤ 0 by norm_num)
    have hKC : 0 ≤ kernelConstant s := by unfold kernelConstant; positivity
    calc
      _ ≤ ‖normalizedBody t p.1 p.2 s - 1‖ + 1 := by
        simpa using norm_add_le (normalizedBody t p.1 p.2 s - 1) (1 : ℂ)
      _ ≤ C + 1 := by nlinarith [hC s hs]
  · rw [normalizedIntegrand, indicator_of_notMem hpt, norm_zero]
    linarith

private lemma normalizedAdjoint_entire {t : ℝ} (ht : 8 ≤ t) :
    Differentiable ℂ (normalizedAdjoint t) := by
  letI := finite_square
  exact entire_integral_of_compact_bound (integrand_measurable ht)
    (Eventually.of_forall (integrand_entire t)) (integrand_compact_bound ht)

private lemma body_timeDerivative_entire {t z u : ℝ} (ht : 8 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    Differentiable ℂ (fun s => deriv (fun y => normalizedBody y z u s) t) := by
  have ht0 : 0 < t := by linarith
  have hAr := (ratio_time_control ht hz hu).1
  have hJr := (jacobianFactor_hasDerivAt ht0 hz.1).differentiableAt
  have heq : (fun s => deriv (fun y => normalizedBody y z u s) t) =
      fun s =>
        ((normalizedPower t z s * (-s - 1 / 2) *
          (((z / 5 * OriginalMovingWindowMoment.width (coordinate t z)) /
            (t ^ 2 * (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))) /
              (coordinate t z / t) : ℝ) : ℂ)) * (weightRatio (coordinate t z) u : ℂ) +
          normalizedPower t z s * ((deriv (fun y : ℝ => weightRatio (coordinate y z) u) t : ℝ) : ℂ)) *
            (jacobianFactor t z : ℂ) +
          (normalizedPower t z s * (weightRatio (coordinate t z) u : ℂ)) *
            ((deriv (fun y : ℝ => jacobianFactor y z) t : ℝ) : ℂ) := by
    funext s
    exact (((normalizedPower_hasDerivAt ht0 hz.1 s).mul hAr.hasDerivAt.ofReal_comp).mul
      hJr.hasDerivAt.ofReal_comp).deriv
  rw [heq]
  unfold normalizedPower
  fun_prop

private lemma integrand_timeDerivative_entire {t : ℝ} (ht : 8 ≤ t)
    (p : ℝ × ℝ) (hp : p ∈ unitSquare) :
    Differentiable ℂ (fun s => deriv (fun y => normalizedIntegrand y s p) t) := by
  by_cases hpt : p ∈ triangle
  · simpa only [normalizedIntegrand, indicator_of_mem hpt] using
      body_timeDerivative_entire ht hp.1 hp.2
  · simp only [normalizedIntegrand, indicator_of_notMem hpt, deriv_const']
    exact differentiable_const _

private lemma normalizedAdjoint_timeDerivative_entire {t : ℝ} (ht : 8 < t) :
    Differentiable ℂ (fun s => deriv (fun y => normalizedAdjoint y s) t) := by
  letI := finite_square
  have hIntegral : Differentiable ℂ
      (fun s => ∫ p in unitSquare, deriv (fun y => normalizedIntegrand y s p) t) := by
    apply entire_integral_of_compact_bound (integrand_derivative_measurable ht)
    · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      exact integrand_timeDerivative_entire ht.le p hp
    · intro K hK
      obtain ⟨C, hC0, hC⟩ := kernelConstant_bounded K hK
      refine ⟨C, ?_⟩
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp s hs
      have hε : t ^ (-6 / 5 : ℝ) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : 1 ≤ t)
          (show (-6 / 5 : ℝ) ≤ 0 by norm_num)
      have hKC : 0 ≤ kernelConstant s := by unfold kernelConstant; positivity
      exact (integrand_derivative_bound ht.le s p hp).trans
        ((mul_le_of_le_one_right hKC hε).trans (hC s hs))
  have heq : (fun s => deriv (fun y => normalizedAdjoint y s) t) =
      (fun s => ∫ p in unitSquare, deriv (fun y => normalizedIntegrand y s p) t) := by
    funext s
    exact (normalizedAdjoint_hasDerivAt ht s).deriv
  rw [heq]
  exact hIntegral

/-- The actual remainder is entire in its Mellin parameter at every tail point. -/
theorem adjointRemainder_entire {t : ℝ} (ht : 8 < t) :
    Differentiable ℂ (adjointRemainder t) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith : t ≠ 0)
  exact ((differentiable_id.neg.sub_const (1 / 2 : ℂ)).const_cpow (.inl ht0)).mul
    ((normalizedAdjoint_entire ht.le).sub_const (1 / 2 : ℂ))

/-- Differentiating the actual remainder in time preserves entire parameter dependence. -/
theorem adjointRemainder_timeDerivative_entire {t : ℝ} (ht : 8 < t) :
    Differentiable ℂ (fun s => deriv (fun y => adjointRemainder y s) t) := by
  have ht0 : 0 < t := by linarith
  have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have heq : (fun s => deriv (fun y => adjointRemainder y s) t) =
      fun s => (-s - 1 / 2) * (t : ℂ) ^ (-s - 1 / 2 - 1) *
          (normalizedAdjoint t s - 1 / 2) +
        (t : ℂ) ^ (-s - 1 / 2) * deriv (fun y => normalizedAdjoint y s) t := by
    funext s
    exact ((principalPower_hasDerivAt ht0 s).mul
      ((normalizedAdjoint_derivative ht s).1.hasDerivAt.sub_const (1 / 2 : ℂ))).deriv
  rw [heq]
  have hp : Differentiable ℂ (fun s : ℂ => (t : ℂ) ^ (-s - 1 / 2)) :=
    (differentiable_id.neg.sub_const (1 / 2 : ℂ)).const_cpow (.inl hne)
  have hp' : Differentiable ℂ (fun s : ℂ => (t : ℂ) ^ (-s - 1 / 2 - 1)) :=
    ((differentiable_id.neg.sub_const (1 / 2 : ℂ)).sub_const 1).const_cpow (.inl hne)
  exact (((differentiable_id.neg.sub_const (1 / 2 : ℂ)).mul hp').mul
    ((normalizedAdjoint_entire ht.le).sub_const (1 / 2 : ℂ))).add
      (hp.mul (normalizedAdjoint_timeDerivative_entire ht))

/-- The actual differentiated remainder has a holomorphic Chebyshev integral. -/
theorem adjointRemainder_tail_holomorphic
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {x0 : ℝ} (hx0 : 8 < x0) :
    DifferentiableOn ℂ
      (fun s => ∫ t in Ioi x0,
        (discrepancy t : ℂ) * deriv (fun y => adjointRemainder y s) t)
      {s : ℂ | (α - 7 / 10) < s.re} := by
  let d : ℂ → ℝ → ℂ := fun s t => deriv (fun y => adjointRemainder y s) t
  have hmeas (s : ℂ) : AEStronglyMeasurable (d s) (volume.restrict (Ioi x0)) :=
    aestronglyMeasurable_deriv (fun t => adjointRemainder t s) _
  have hd : ∀ᵐ t : ℝ ∂volume.restrict (Ioi x0), Differentiable ℂ (fun s => d s t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact adjointRemainder_timeDerivative_entire (hx0.trans ht)
  apply ForwardKernel.RemainderContinuation.remainder_integral_holomorphic hα hE (by linarith)
    (fun s _ => hmeas s)
    (fun t ht => (adjointRemainder_timeDerivative_entire (hx0.trans ht)).differentiableOn)
    (fun s _ => parameter_derivative_measurable hmeas hd s)
  intro K hK _
  obtain ⟨C, hC, hbound⟩ := inverseAdjoint_uniform_C1_remainder K hK
  refine ⟨C, hC.le, ?_⟩
  intro s hs t ht
  have hb := (hbound s hs t (hx0.trans_le ht)).2
  convert hb using 1
  rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < t)]
  congr 2
  ring

#print axioms adjointRemainder_entire
#print axioms adjointRemainder_timeDerivative_entire
#print axioms adjointRemainder_tail_holomorphic

end

end D5.S3.Arith.Robin.ForwardKernel.Analytic
