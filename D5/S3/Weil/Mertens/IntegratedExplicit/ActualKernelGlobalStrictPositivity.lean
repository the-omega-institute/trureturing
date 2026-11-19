/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelGlobalStrictPositivity
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelGlobalStrictPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Abs]
   utility: none
   digest: Under RH the original complete arithmetic kernel has strictly positive finite Gram matrices at arbitrary distinct real nodes. -/

import D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

/-! Full arithmetic Fourier positivity and the isolated logarithmic cusp. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Set Matrix Asymptotics
open scoped Topology BigOperators ComplexOrder
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity

private def weight (k : ℕ) : ℝ := 1 / (1 / 4 + (actualZero k).im ^ 2)

/-- The complete series retains every analytic occurrence. Taking real parts
avoids any need to reindex by conjugate occurrences. -/
private lemma actual_cosine_hasSum (hRH : RiemannHypothesis) (t : ℝ) :
    HasSum (fun k : ℕ => ((weight k * Real.cos ((actualZero k).im * t) : ℝ) : ℂ))
      (K t : ℂ) := by
  have hline (k : ℕ) : (actualZero k).re = 1 / 2 := by
    simpa only [actualZero, D5.S3.Weil.Convention.criticalAbscissa] using
      zeroData_zero_on_critical_line_of_rh hRH actualData (actualOccurrenceEquiv k).1
  have hcoeff (k : ℕ) : actualCoeff k = (weight k : ℂ) := by
    have hd : actualZero k * (1 - actualZero k) =
        ((1 / 4 + (actualZero k).im ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
          hline k] <;> ring
    simp only [actualCoeff, weight, hd, Complex.ofReal_div, Complex.ofReal_one]
  have hkernel : (Real.exp (-|t| / 2) : ℂ) * actualH |t| = (K t : ℂ) := by
    by_cases ht : t = 0
    · subst t
      have hzero : actualH 0 = (firstLiMass : ℂ) := by
        simpa only [actualH, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
          using actualCoeff_hasSum.tsum_eq
      simp [hzero, K_zero]
    · rw [actual_integrated_explicit_formula (abs_pos.mpr ht)]
      simp only [K, Complex.ofReal_mul]
  have hs : HasSum
      (fun k : ℕ => (Real.exp (-|t| / 2) : ℂ) *
        (actualCoeff k * Complex.exp (((|t| : ℝ) : ℂ) * actualZero k)))
      ((Real.exp (-|t| / 2) : ℂ) * actualH |t|) :=
    (actualH_summable |t|).hasSum.mul_left _
  have hterm (k : ℕ) :
      ((Real.exp (-|t| / 2) : ℂ) *
        (actualCoeff k * Complex.exp (((|t| : ℝ) : ℂ) * actualZero k))).re =
      weight k * Real.cos ((actualZero k).im * t) := by
    have hcos : Real.cos (|t| * (actualZero k).im) =
        Real.cos ((actualZero k).im * t) := by
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht, mul_comm]
      · rw [abs_of_nonpos ht, neg_mul, Real.cos_neg, mul_comm]
    have hexp : Real.exp (-|t| / 2) * Real.exp (|t| * (1 / 2)) = 1 := by
      rw [← Real.exp_add, show -|t| / 2 + |t| * (1 / 2) = 0 by ring,
        Real.exp_zero]
    rw [hcoeff k]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.exp_re, Complex.mul_im, add_zero, hline k]
    rw [hcos]
    calc
      Real.exp (-|t| / 2) *
          (weight k * (Real.exp (|t| * (1 / 2)) *
            Real.cos ((actualZero k).im * t))) =
          (Real.exp (-|t| / 2) * Real.exp (|t| * (1 / 2))) *
            (weight k * Real.cos ((actualZero k).im * t)) := by ring
      _ = _ := by rw [hexp, one_mul]
  apply Complex.hasSum_ofReal.mpr
  convert Complex.hasSum_re hs using 1
  · funext k
    exact (hterm k).symm
  · rw [hkernel]
    rfl

private lemma actual_positiveDefinite (hRH : RiemannHypothesis) :
    D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (fun t : ℝ => (K t : ℂ)) := by
  apply D5.S3.Analytic.Fourier.PositiveDefinite.Closure.limit (l := atTop)
    (f := fun N t => ∑ k ∈ Finset.range N,
      (weight k : ℂ) * (Real.cos ((actualZero k).im * t) : ℂ))
  · intro N
    apply D5.S3.Analytic.Fourier.PositiveDefinite.Closure.sum
    intro k _
    apply D5.S3.Analytic.Fourier.PositiveDefinite.Closure.smul
      (D5.S3.Analytic.Fourier.PositiveDefinite.Closure.cos _)
    dsimp only [weight]
    positivity
  · intro t
    simpa only [Complex.ofReal_mul] using (actual_cosine_hasSum hRH t).tendsto_sum_nat

/-- The finite ramp formula supplies increment bounds at every nonzero point,
including each prime-power activation point. -/
private lemma K_increment_bigO {r : ℝ} (hr : r ≠ 0) :
    (fun h : ℝ => K (r + h) - K r) =O[𝓝 0] (fun h : ℝ => h) := by
  classical
  let N : ℕ := ⌈Real.exp |r| + 1⌉₊ + 1
  have hrN : Real.exp |r| < (N : ℝ) := by
    have hc := Nat.le_ceil (Real.exp |r| + 1)
    dsimp only [N]
    push_cast
    linarith
  let S : ℝ → ℝ := fun t => ∑ n ∈ Finset.range N, mangoldtRamp n (Real.exp |t|)
  let E : ℝ → ℝ := fun t => Real.exp (-|t| / 2)
  let g : ℝ → ℝ := fun t => E t *
    (-(Real.exp |t|) * |t| + (1 + Real.eulerMascheroniConstant) * Real.exp |t| -
      Real.log (2 * Real.pi) + trivialT |t|)
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t|) r := differentiableAt_abs hr
  have hexp : DifferentiableAt ℝ (fun t : ℝ => Real.exp |t|) r := habs.exp
  have hE : DifferentiableAt ℝ E r := (habs.neg.div_const 2).exp
  have hT : DifferentiableAt ℝ (fun t : ℝ => trivialT |t|) r :=
    (trivialT_derivative (abs_pos.mpr hr)).differentiableAt.comp r habs
  have hg : DifferentiableAt ℝ g r := by
    dsimp only [g]
    exact hE.mul ((((hexp.neg.mul habs).add
      (hexp.const_mul (1 + Real.eulerMascheroniConstant))).sub_const
        (Real.log (2 * Real.pi))).add hT)
  have hramps (n : ℕ) :
      (fun t => mangoldtRamp n (Real.exp |t|) - mangoldtRamp n (Real.exp |r|))
        =O[𝓝 r] (fun t : ℝ => t - r) := by
    have hd : DifferentiableAt ℝ (fun t : ℝ => Real.exp |t| / (n : ℝ) - 1) r :=
      (hexp.div_const (n : ℝ)).sub_const 1
    obtain ⟨C, hC⟩ := hd.isBigO_sub.bound
    have hm : (fun t => max (Real.exp |t| / (n : ℝ) - 1) 0 -
        max (Real.exp |r| / (n : ℝ) - 1) 0) =O[𝓝 r] (fun t : ℝ => t - r) := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [hC] with t ht
      exact (show ‖max (Real.exp |t| / (n : ℝ) - 1) 0 -
          max (Real.exp |r| / (n : ℝ) - 1) 0‖ ≤
          ‖(Real.exp |t| / (n : ℝ) - 1) - (Real.exp |r| / (n : ℝ) - 1)‖ by
        simpa only [Real.norm_eq_abs] using abs_max_sub_max_le_abs
          (Real.exp |t| / (n : ℝ) - 1) (Real.exp |r| / (n : ℝ) - 1) 0).trans ht
    simpa only [mangoldtRamp, mul_sub] using
      hm.const_mul_left (ArithmeticFunction.vonMangoldt n)
  have hS : (fun t => S t - S r) =O[𝓝 r] (fun t : ℝ => t - r) := by
    simpa only [S, Finset.sum_sub_distrib] using
      (Asymptotics.IsBigO.fun_sum (s := Finset.range N) (fun n _ => hramps n))
  have hES : (fun t => E t * S t - E r * S r) =O[𝓝 r] (fun t : ℝ => t - r) := by
    have hfirst := (hE.continuousAt.tendsto.isBigO_one ℝ).mul hS
    simp only [one_mul] at hfirst
    exact (hfirst.add (hE.isBigO_sub.const_mul_left (S r))).congr_left
      (fun t => by ring)
  have hlocal : K =ᶠ[𝓝 r] (fun t => E t * S t + g t) := by
    have hlt : ∀ᶠ t : ℝ in 𝓝 r, Real.exp |t| < (N : ℝ) :=
      hexp.continuousAt.tendsto.eventually_lt_const hrN
    filter_upwards [hlt] with t ht
    rw [K, U_eq_complete_ramps (Real.exp_nonneg _),
      mangoldtPart_eq_range (Real.exp_nonneg _) ht, Real.log_exp]
    dsimp only [E, S, g]
    ring
  have hKr : K r = E r * S r + g r := hlocal.self_of_nhds
  have hbase : (fun t => K t - K r) =O[𝓝 r] (fun t : ℝ => t - r) := by
    apply (hES.add hg.isBigO_sub).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hlocal] with t ht
    rw [ht, hKr]
    ring
  have hshift : Tendsto (fun h : ℝ => r + h) (𝓝 0) (𝓝 r) := by
    have hc : Continuous (fun h : ℝ => r + h) := continuous_const.add continuous_id
    simpa using hc.tendsto (0 : ℝ)
  simpa only [Function.comp_def, add_sub_cancel_left] using hbase.comp_tendsto hshift

/-- Full endpoint continuity and the public derivative limit exclude every
linear increment bound at zero. -/
private lemma K_origin_not_bigO :
    ¬ (fun h : ℝ => K h - K 0) =O[𝓝 0] (fun h : ℝ => h) := by
  intro h
  obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp h
  have hD : ∀ᶠ u : ℝ in 𝓝[>] 0, D1 u < -(C + 1) :=
    D1_atBot.eventually (eventually_lt_atBot (-(C + 1)))
  obtain ⟨δ, hδ, hDδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hD
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < min δ (Real.log 2) := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact Iio_mem_nhds (lt_min hδ hlog)
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖K t - K 0‖ ≤ C * ‖t‖ :=
    hbound.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htbound, htsmall, htpos⟩ :=
    (hb.and (hsmall.and self_mem_nhdsWithin)).exists
  change 0 < t at htpos
  have htδ : t < δ := htsmall.trans_le (min_le_left _ _)
  have htlog : t < Real.log 2 := htsmall.trans_le (min_le_right _ _)
  obtain ⟨u, hu, heu⟩ := exists_hasDerivAt_eq_slope K D1 htpos
    K_continuous.continuousOn
    (fun u hu => hasDerivAt_K hu.1 (hu.2.trans htlog))
  have hdu : D1 u < -(C + 1) := hDδ ⟨hu.1, hu.2.trans htδ⟩
  rw [heu, sub_zero] at hdu
  have hslope : K t - K 0 < -(C + 1) * t := (div_lt_iff₀ htpos).mp hdu
  simp only [Real.norm_eq_abs, abs_of_pos htpos] at htbound
  have hlower := (abs_le.mp htbound).1
  nlinarith

/-- Under RH alone, every finite injective real-node configuration has a
strictly positive complex Gram matrix for the original arithmetic K. -/
theorem actual_kernel_strict_gram_of_rh (hRH : RiemannHypothesis)
    (n : ℕ) (x : Fin n → ℝ) (hx : Function.Injective x) :
    Matrix.PosDef (fun i j => (K (x j - x i) : ℂ)) := by
  apply D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity.posDef_of_isolated_non_lipschitz
    (V := ℝ) (k := fun t => (K t : ℂ))
    (actual_positiveDefinite hRH) ?_ ?_ n x hx
  · intro r hr
    obtain ⟨C, hC⟩ := (K_increment_bigO hr).bound
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hC] with h hh
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh
  · intro h
    apply K_origin_not_bigO
    obtain ⟨C, hC⟩ := h.bound
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hC] with t ht
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using ht

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity
