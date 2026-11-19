/- GID: D5/S3/Weil/Mertens/MobiusDyadicEnergy/FiniteResponse
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite zero-forced response and square-integral transfer for the signed Möbius energy proof. -/

import D5.S3.Weil.Mertens.MobiusDyadicEnergy.Kernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import D5.S3.Analytic.Fourier.ConvolutionL2
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace CausalResolventL1

private def beta (lambda : ℂ) : ℝ := lambda.re + 1 / 2

private def damped (a : ℝ → ℂ) (lambda : ℂ) (u : ℝ) : ℂ :=
  a u * Complex.exp (-lambda * (u : ℂ))

private def dampedZero (a : ℝ → ℂ) (lambda : ℂ) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator (damped a lambda)

private def primitive (a : ℝ → ℂ) (lambda : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (lambda * (t : ℂ)) *
    (∫ u in (0 : ℝ)..t, dampedZero a lambda u ∂volume)

private def resolvent (a : ℝ → ℂ) (lambda : ℂ) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator (primitive a lambda)

private def envelope (t : ℝ) : ℝ := (2 * t + 6) * Real.exp (-t / 2)

private theorem beta_ge_half {lambda : ℂ} (hlambda : 0 ≤ lambda.re) :
    (1 / 2 : ℝ) ≤ beta lambda := by
  dsimp [beta]
  linarith

private theorem exp_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi 0) volume :=
  integrableOn_exp_mul_Ioi (by linarith : -b < 0) 0

private theorem linear_exp_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-b * u)) (Ioi 0) volume := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (1 : ℝ)) (p := (1 : ℝ)) (b := b)
      (by norm_num) (by norm_num) hb)

private theorem polynomial_exp_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-b * u)) (Ioi 0) volume := by
  refine ((exp_integrable hb).add (linear_exp_integrable hb)).congr_fun
    (fun u _ => ?_) measurableSet_Ioi
  dsimp
  ring

private def tailPrimitive (b u : ℝ) : ℝ :=
  -(((1 + u) / b + 1 / b ^ 2) * Real.exp (-b * u))

private theorem tailPrimitive_hasDerivAt {b : ℝ} (hb : 0 < b) (u : ℝ) :
    HasDerivAt (tailPrimitive b) ((1 + u) * Real.exp (-b * u)) u := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hp := (((hasDerivAt_id u).const_add 1).div_const b).add_const (1 / b ^ 2)
  have he := ((hasDerivAt_id u).const_mul (-b)).exp
  change HasDerivAt (fun x : ℝ => -(((1 + x) / b + 1 / b ^ 2) *
    Real.exp (-b * x))) ((1 + u) * Real.exp (-b * u)) u
  convert (hp.mul he).neg using 1
  · rfl
  · dsimp
    field_simp [hb0]
    ring

private theorem tailPrimitive_tendsto {b : ℝ} (hb : 0 < b) :
    Tendsto (tailPrimitive b) atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-b * u)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb
  have hue : Tendsto (fun u : ℝ => u * Real.exp (-b * u)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
  have h := ((he.const_mul (1 / b + 1 / b ^ 2)).add
    (hue.const_mul (1 / b))).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  apply h.congr'
  filter_upwards with u
  dsimp [tailPrimitive]
  ring

/-- Finiteness precedes the use of the improper FTC and the exact tail evaluation. -/
private theorem polynomial_exp_tail {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    (∫ u in Ioi t, (1 + u) * Real.exp (-b * u) ∂volume) =
      Real.exp (-b * t) * ((1 + t) / b + 1 / b ^ 2) := by
  have hi : IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-b * u))
      (Ioi t) volume :=
    (polynomial_exp_integrable hb).mono_set (Ioi_subset_Ioi ht)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u (_ : u ∈ Ici t) => tailPrimitive_hasDerivAt hb u)
    hi (tailPrimitive_tendsto hb)
  simpa only [tailPrimitive, sub_neg_eq_add, zero_add, mul_comm] using h

private theorem damped_measurable {a : ℝ → ℂ} (ha : Measurable a) (lambda : ℂ) :
    Measurable (damped a lambda) := by
  unfold damped
  exact ha.mul (by fun_prop)

/-- Pointwise domination uses no sign condition on the complex input. -/
private theorem norm_damped_le {a : ℝ → ℂ} {lambda : ℂ}
    (ha : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖damped a lambda t‖ ≤ (1 + t) * Real.exp (-beta lambda * t) := by
  have hn : ‖damped a lambda t‖ = ‖a t‖ * Real.exp (-lambda.re * t) := by
    simp [damped, norm_mul, Complex.norm_exp, Complex.mul_re]
  rw [hn]
  calc
    ‖a t‖ * Real.exp (-lambda.re * t) ≤
        ((1 + t) * Real.exp (-t / 2)) * Real.exp (-lambda.re * t) :=
      mul_le_mul_of_nonneg_right (ha t ht) (Real.exp_pos _).le
    _ = (1 + t) * Real.exp (-beta lambda * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [beta]
      ring

/-- Actual absolute convergence, independent of any vanishing-integral hypothesis. -/
private theorem damped_integrableOn {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re) :
    IntegrableOn (damped a lambda) (Ioi 0) volume := by
  have hb : 0 < beta lambda := lt_of_lt_of_le (by norm_num) (beta_ge_half hlambda)
  refine (polynomial_exp_integrable hb).mono'
    (damped_measurable ha lambda).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_damped_le hbound ht.le

private theorem damped_integrableOn_tail {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (damped a lambda) (Ioi t) volume :=
  (damped_integrableOn ha hbound hlambda).mono_set (Ioi_subset_Ioi ht)

private theorem dampedZero_integrable {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re) :
    Integrable (dampedZero a lambda) volume := by
  have hi : IntegrableOn (damped a lambda) (Ici 0) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (damped_integrableOn ha hbound hlambda)
  exact hi.integrable_indicator measurableSet_Ici

private theorem primitive_continuous {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re) : Continuous (primitive a lambda) := by
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (lambda * (t : ℂ)))).mul
    ((dampedZero_integrable ha hbound hlambda).continuous_primitive 0)

private theorem resolvent_measurable {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re) : Measurable (resolvent a lambda) :=
  (primitive_continuous ha hbound hlambda).measurable.indicator measurableSet_Ici

/-- This is exactly the finite-primitive definition in the specification. -/
private theorem q_eq_primitive (a : ℝ → ℂ) (lambda : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    resolvent a lambda t = Complex.exp (lambda * (t : ℂ)) *
      (∫ u in (0 : ℝ)..t, a u * Complex.exp (-lambda * (u : ℂ)) ∂volume) := by
  rw [resolvent, indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht), primitive]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht] using hu
  exact indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu'.1) _

private theorem q_eq_zero_of_neg (a : ℝ → ℂ) (lambda : ℂ) {t : ℝ} (ht : t < 0) :
    resolvent a lambda t = 0 := by
  simp [resolvent, not_le.mpr ht]

/-- Both the full integral and the tail are integrable before cancellation is used. -/
private theorem q_eq_neg_tail {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re)
    (hzero : (∫ u in Ioi (0 : ℝ), damped a lambda u ∂volume) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    resolvent a lambda t = -Complex.exp (lambda * (t : ℂ)) *
      (∫ u in Ioi t, a u * Complex.exp (-lambda * (u : ℂ)) ∂volume) := by
  have hi := damped_integrableOn ha hbound hlambda
  have htail := damped_integrableOn_tail ha hbound hlambda ht
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi' hi htail
  rw [hzero, zero_sub] at hsplit
  rw [q_eq_primitive a lambda ht]
  change Complex.exp (lambda * (t : ℂ)) *
      (∫ u in (0 : ℝ)..t, damped a lambda u ∂volume) = _
  rw [← hsplit]
  simp only [damped, mul_neg, neg_mul]

/-- The sharper beta-dependent bound, including beta = 1/2. -/
private theorem norm_q_le_beta {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re)
    (hzero : (∫ u in Ioi (0 : ℝ), damped a lambda u ∂volume) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖resolvent a lambda t‖ ≤ Real.exp (-t / 2) *
      ((1 + t) / beta lambda + 1 / (beta lambda) ^ 2) := by
  have hb : 0 < beta lambda := lt_of_lt_of_le (by norm_num) (beta_ge_half hlambda)
  have hd := damped_integrableOn_tail ha hbound hlambda ht
  have he : IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-beta lambda * u))
      (Ioi t) volume :=
    (polynomial_exp_integrable hb).mono_set (Ioi_subset_Ioi ht)
  have htail : ‖∫ u in Ioi t, damped a lambda u ∂volume‖ ≤
      Real.exp (-beta lambda * t) *
        ((1 + t) / beta lambda + 1 / (beta lambda) ^ 2) := by
    calc
      _ ≤ ∫ u in Ioi t, ‖damped a lambda u‖ ∂volume :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in Ioi t, (1 + u) * Real.exp (-beta lambda * u) ∂volume := by
        apply integral_mono_ae hd.norm he
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact norm_damped_le hbound (ht.trans hu.le)
      _ = _ := polynomial_exp_tail hb ht
  rw [q_eq_neg_tail ha hbound hlambda hzero ht, norm_mul, norm_neg, Complex.norm_exp]
  have hn : (lambda * (t : ℂ)).re = lambda.re * t := by simp
  rw [hn]
  calc
    Real.exp (lambda.re * t) *
        ‖∫ u in Ioi t, a u * Complex.exp (-lambda * (u : ℂ)) ∂volume‖ ≤
        Real.exp (lambda.re * t) *
          (Real.exp (-beta lambda * t) *
            ((1 + t) / beta lambda + 1 / (beta lambda) ^ 2)) :=
      mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [beta]
      ring

theorem norm_q_le {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re)
    (hzero : (∫ u in Ioi (0 : ℝ), damped a lambda u ∂volume) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖resolvent a lambda t‖ ≤ (2 * t + 6) * Real.exp (-t / 2) := by
  have hbhalf := beta_ge_half hlambda
  have hb : 0 < beta lambda := lt_of_lt_of_le (by norm_num) hbhalf
  have hi : 1 / beta lambda ≤ 2 := (div_le_iff₀ hb).2 (by linarith)
  have hi2 : 1 / (beta lambda) ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).2
    nlinarith [sq_nonneg (beta lambda - 1 / 2)]
  have hc : (1 + t) / beta lambda + 1 / (beta lambda) ^ 2 ≤ 2 * t + 6 := by
    calc
      _ ≤ (1 + t) * 2 + 4 := add_le_add
        (by simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ 1 + t)) hi2
      _ = _ := by ring
  exact (norm_q_le_beta ha hbound hlambda hzero ht).trans
    (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hc (Real.exp_pos (-t / 2)).le)

private theorem envelope_integrable : IntegrableOn envelope (Ioi 0) volume := by
  have h1 := (linear_exp_integrable (b := (1 / 2 : ℝ)) (by norm_num)).const_mul 2
  have h0 := (exp_integrable (b := (1 / 2 : ℝ)) (by norm_num)).const_mul 6
  have hsum : IntegrableOn (fun t : ℝ => 2 * (t * Real.exp (-(1 / 2 : ℝ) * t)) + 6 * Real.exp (-(1 / 2 : ℝ) * t)) (Ioi 0) volume := h1.add h0
  refine hsum.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp [envelope]
  have he : -(1 / 2 : ℝ) * t = -t / 2 := by ring
  rw [he]
  ring

private theorem integral_envelope : (∫ t in Ioi (0 : ℝ), envelope t ∂volume) = 20 := by
  have hp : IntegrableOn (fun t : ℝ => (1 + t) * Real.exp (-(1 / 2 : ℝ) * t))
      (Ioi 0) volume := polynomial_exp_integrable (by norm_num)
  have he : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t))
      (Ioi 0) volume := exp_integrable (by norm_num)
  have hpval : (∫ t in Ioi (0 : ℝ), (1 + t) * Real.exp (-(1 / 2 : ℝ) * t)
      ∂volume) = 6 := by
    have h := polynomial_exp_tail (b := (1 / 2 : ℝ)) (t := 0) (by norm_num) le_rfl
    norm_num at h
    simpa only [neg_mul] using h
  have heval : (∫ t in Ioi (0 : ℝ), Real.exp (-(1 / 2 : ℝ) * t) ∂volume) = 2 := by
    have h := integral_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0
    norm_num at h
    simpa only [neg_mul] using h
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        2 * ((1 + t) * Real.exp (-(1 / 2 : ℝ) * t)) +
          4 * Real.exp (-(1 / 2 : ℝ) * t) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp [envelope]
      have hexp : -(1 / 2 : ℝ) * t = -t / 2 := by ring
      rw [hexp]
      ring
    _ = 20 := by
      rw [integral_add (hp.const_mul 2) (he.const_mul 4),
        integral_const_mul, integral_const_mul, hpval, heval]
      norm_num

private theorem q_integrableOn {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re)
    (hzero : (∫ u in Ioi (0 : ℝ), damped a lambda u ∂volume) = 0) :
    IntegrableOn (resolvent a lambda) (Ioi 0) volume := by
  refine envelope_integrable.mono'
    (resolvent_measurable ha hbound hlambda).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_q_le ha hbound hlambda hzero ht.le

private theorem integral_norm_q_le_twenty {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re)
    (hzero : (∫ u in Ioi (0 : ℝ), damped a lambda u ∂volume) = 0) :
    (∫ t in Ioi (0 : ℝ), ‖resolvent a lambda t‖ ∂volume) ≤ 20 := by
  have hi := q_integrableOn ha hbound hlambda hzero
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), envelope t ∂volume := by
      apply integral_mono_ae hi.norm envelope_integrable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_q_le ha hbound hlambda hzero ht.le
    _ = 20 := integral_envelope

/-- Genuine global L1 membership of the causal zero extension. -/
private theorem q_integrable {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re)
    (hzero : (∫ u in Ioi (0 : ℝ), damped a lambda u ∂volume) = 0) :
    Integrable (resolvent a lambda) volume := by
  have hi : IntegrableOn (resolvent a lambda) (Ici 0) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (q_integrableOn ha hbound hlambda hzero)
  have hext : (Ici (0 : ℝ)).indicator (resolvent a lambda) = resolvent a lambda := by
    ext t
    by_cases ht : 0 ≤ t
    · simp [ht]
    · simp [resolvent, ht]
  simpa only [hext] using hi.integrable_indicator measurableSet_Ici

/-- Exact zero-extension bridge, including the null endpoint at zero. -/
private theorem integral_norm_q_eq_halfLine (a : ℝ → ℂ) (lambda : ℂ) :
    (∫ t : ℝ, ‖resolvent a lambda t‖ ∂volume) =
      ∫ t in Ioi (0 : ℝ), ‖resolvent a lambda t‖ ∂volume := by
  have hext : (Ici (0 : ℝ)).indicator (fun t => ‖resolvent a lambda t‖) =
      (fun t => ‖resolvent a lambda t‖) := by
    ext t
    by_cases ht : 0 ≤ t
    · simp [ht]
    · simp [resolvent, ht]
  calc
    _ = ∫ t : ℝ, (Ici (0 : ℝ)).indicator (fun t => ‖resolvent a lambda t‖) t ∂volume :=
      congrArg (fun f : ℝ → ℝ => ∫ t, f t ∂volume) hext.symm
    _ = ∫ t in Ici (0 : ℝ), ‖resolvent a lambda t‖ ∂volume :=
      integral_indicator measurableSet_Ici
    _ = _ := integral_Ici_eq_integral_Ioi

private theorem integral_norm_q_global_le_twenty {a : ℝ → ℂ} (ha : Measurable a)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖a t‖ ≤ (1 + t) * Real.exp (-t / 2))
    {lambda : ℂ} (hlambda : 0 ≤ lambda.re)
    (hzero : (∫ u in Ioi (0 : ℝ), damped a lambda u ∂volume) = 0) :
    (∫ t : ℝ, ‖resolvent a lambda t‖ ∂volume) ≤ 20 := by
  rw [integral_norm_q_eq_halfLine]
  exact integral_norm_q_le_twenty ha hbound hlambda hzero

end CausalResolventL1

open Set MeasureTheory Filter
open scoped Topology Convolution BigOperators NNReal ENNReal

namespace MobiusCausalPrefixEnergy

open D5.S3.Analytic.Fourier.ConvolutionL2 (complex_l2_integral)

private abbrev aC (t : ℝ) : ℂ := (MobiusCausalKernel.a t : ℂ)
abbrev hC (t : ℝ) : ℂ := (MobiusCausalKernel.h t : ℂ)
def lambda (rho : ℂ) : ℂ := rho - 1 / 2
def q (rho : ℂ) : ℝ → ℂ := CausalResolventL1.resolvent aC (lambda rho)
def causal (f g : ℝ → ℂ) (t : ℝ) : ℂ := ∫ u in (0 : ℝ)..t, f u * g (t-u)
def response (rho : ℂ) (t : ℝ) : ℂ := causal (q rho) hC t
def explicitOutput (rho : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (lambda rho * (t : ℂ)) -
    (1 + rho * (t : ℂ)) * Complex.exp (-(t : ℂ) / 2)) / rho^2

private def cut {E : Type*} [Zero E] (T : ℝ) (f : ℝ → E) : ℝ → E :=
  (Icc 0 T).indicator f

lemma bounded_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → E} (hf : Measurable f) {T M : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) : IntervalIntegrable f volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
  refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    hf.aestronglyMeasurable (M := M) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hb t ⟨ht.1.le, ht.2⟩

private lemma cut_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → E} (hf : Measurable f) {T M : ℝ}
    (hb : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) : Integrable (cut T f) := by
  have hi : IntegrableOn f (Icc 0 T) := by
    refine Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      hf.aestronglyMeasurable (M := M) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hb t ht
  exact hi.integrable_indicator measurableSet_Icc

lemma cut_bound {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {T M : ℝ} (hM : 0 ≤ M) (hb : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) (t : ℝ) :
    ‖cut T f t‖ ≤ M := by
  by_cases ht : t ∈ Icc 0 T
  · simpa only [cut, indicator_of_mem ht] using hb t ht
  · simpa only [cut, indicator_of_notMem ht, norm_zero] using hM

private lemma cut_negative {E : Type*} [Zero E] (f : ℝ → E) (T : ℝ)
    {t : ℝ} (ht : t < 0) : cut T f t = 0 := by
  exact indicator_of_notMem (fun h : t ∈ Icc 0 T => (not_le_of_gt ht) h.1) f

private def frac (t : ℝ) : ℝ := Int.fract (Real.exp t)

private lemma frac_measurable : Measurable frac := Real.measurable_exp.fract

private lemma frac_interval (a b : ℝ) : IntervalIntegrable frac volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (by simp [uIoc])
    frac_measurable.aestronglyMeasurable (M := 1) ?_
  filter_upwards with t
  simpa only [frac, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg (Real.exp t))] using
    (Int.fract_lt_one (Real.exp t)).le

lemma aC_measurable : Measurable aC := by
  have hp : Continuous (fun t : ℝ => ∫ u in (0 : ℝ)..t, frac u) :=
    intervalIntegral.continuous_primitive frac_interval 0
  exact Complex.continuous_ofReal.measurable.comp
    ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-t/2))).mul
      ((measurable_const.sub frac_measurable).add hp.measurable))

lemma aC_envelope (t : ℝ) (ht : 0 ≤ t) :
    ‖aC t‖ ≤ (1+t)*Real.exp (-t/2) := by
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..t, frac u :=
    intervalIntegral.integral_nonneg_of_forall ht (fun u => Int.fract_nonneg _)
  have h1 : (∫ u in (0 : ℝ)..t, frac u) ≤ t := by
    have h := intervalIntegral.integral_mono_on ht (frac_interval 0 t)
      intervalIntegrable_const (fun u _ => (Int.fract_lt_one (Real.exp u)).le)
    simpa using h
  have ha0 : 0 ≤ MobiusCausalKernel.a t := by
    unfold MobiusCausalKernel.a
    exact mul_nonneg (Real.exp_pos _).le (by
      change 0 ≤ 1-frac t + ∫ u in (0 : ℝ)..t, frac u
      have hf : frac t < 1 := Int.fract_lt_one (Real.exp t)
      linarith)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  unfold MobiusCausalKernel.a
  change Real.exp (-t/2) * (1-frac t + ∫ u in (0 : ℝ)..t, frac u) ≤ _
  have hb : 1-frac t + (∫ u in (0 : ℝ)..t, frac u) ≤ 1+t := by
    have hf : 0 ≤ frac t := Int.fract_nonneg (Real.exp t)
    linarith
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (mul_comm _ _)

private lemma aC_local_bound {T t : ℝ} (ht : t ∈ Icc 0 T) : ‖aC t‖ ≤ 1+T := by
  have he : Real.exp (-t/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
  calc
    _ ≤ (1+t)*Real.exp (-t/2) := aC_envelope t ht.1
    _ ≤ (1+t)*1 := mul_le_mul_of_nonneg_left he (by linarith [ht.1])
    _ ≤ 1+T := by linarith [ht.2]

lemma hC_measurable : Measurable hC := by
  let F : ℕ → ℝ := fun N => ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℝ)/(n : ℝ)
  have hm : Measurable
      D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.mobiusPartialSum :=
    (measurable_of_countable F).comp Nat.measurable_floor
  exact Complex.continuous_ofReal.measurable.comp
    ((by fun_prop : Measurable (fun t : ℝ => Real.exp (t/2))).mul
      (hm.comp Real.measurable_exp))

/-- Cutoff normalization only: reuse the stronger frozen public reciprocal bound. -/
lemma hC_local_bound {T t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖hC t‖ ≤ Real.exp (T/2) := by
  have hm := D5.S3.Arith.MoebiusLogarithmic.abs_reciprocalSum_le_one (Real.exp t)
  have hc : Finset.Icc 1 ⌊Real.exp t⌋₊ = Finset.Ioc 0 ⌊Real.exp t⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  change |D5.S3.Arith.MoebiusLogarithmic.reciprocalSum (Real.exp t)| ≤ 1 at hm
  rw [Complex.norm_real, Real.norm_eq_abs, MobiusCausalKernel.h, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have hm' :
      |D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.mobiusPartialSum
        (Real.exp t)| ≤ 1 := by
    simpa only [D5.S3.Arith.MoebiusLogarithmic.reciprocalSum,
      D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.mobiusPartialSum, hc] using hm
  calc
    _ ≤ Real.exp (t/2)*1 := mul_le_mul_of_nonneg_left hm' (Real.exp_pos _).le
    _ ≤ Real.exp (T/2) := by simpa using Real.exp_le_exp.mpr (by linarith [ht.2])

lemma rho_ne_zero {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re) : rho ≠ 0 := by
  intro hz
  rw [hz] at hh
  norm_num at hh

lemma lambda_re_nonneg {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re) :
    0 ≤ (lambda rho).re := by simp only [lambda, Complex.sub_re]; norm_num; linarith

lemma actual_zero {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) :
    (∫ u in Ioi (0 : ℝ), CausalResolventL1.damped aC (lambda rho) u) = 0 := by
  simpa only [CausalResolventL1.damped, lambda] using
    (MobiusKernelLaplace.at_nontrivial_zero hh hl hz).2

lemma q_measurable {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re) : Measurable (q rho) :=
  CausalResolventL1.resolvent_measurable aC_measurable aC_envelope (lambda_re_nonneg hh)

/-- The supplier computes 20 by integrating (2t+6)exp(-t/2): 2*4+6*2=20.
No unsupported numerical kernel budget is added here. -/
private lemma q_budget {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) :
    Integrable (q rho) ∧ (∫ t : ℝ, ‖q rho t‖) ≤ 20 := by
  have h0 := actual_zero hh hl hz
  exact ⟨CausalResolventL1.q_integrable aC_measurable aC_envelope
      (lambda_re_nonneg hh) h0,
    CausalResolventL1.integral_norm_q_global_le_twenty aC_measurable aC_envelope
      (lambda_re_nonneg hh) h0⟩

lemma q_local_bound {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖q rho t‖ ≤ 2*T+6 := by
  have hb := CausalResolventL1.norm_q_le aC_measurable aC_envelope
    (lambda_re_nonneg hh) (actual_zero hh hl hz) ht.1
  have he : Real.exp (-t/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
  calc
    _ ≤ (2*t+6)*Real.exp (-t/2) := hb
    _ ≤ (2*t+6)*1 := mul_le_mul_of_nonneg_left he (by linarith [ht.1])
    _ ≤ 2*T+6 := by linarith [ht.2]

private abbrev cmul : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

private lemma convolution_negative {f g : ℝ → ℂ}
    (hf : ∀ x < 0, f x = 0) (hg : ∀ x < 0, g x = 0)
    {t : ℝ} (ht : t < 0) : convolution f g cmul volume t = 0 := by
  change (∫ u : ℝ, f u * g (t-u)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hu : u < 0
  · simp only [hf u hu, zero_mul, Pi.zero_apply]
  · simp only [hg (t-u) (by linarith), mul_zero, Pi.zero_apply]

/-- Exact closed-interval bridge. Endpoints are removed only by the existing
Lebesgue Icc/Ioc equality, never by pretending the literal h(0) vanishes. -/
private lemma convolution_of_causal {f g : ℝ → ℂ}
    (hf : ∀ x < 0, f x = 0) (hg : ∀ x < 0, g x = 0)
    {t : ℝ} (ht : 0 ≤ t) : convolution f g cmul volume t = causal f g t := by
  change (∫ u : ℝ, f u * g (t-u)) = _
  calc
    _ = ∫ u : ℝ, (Icc 0 t).indicator (fun u => f u * g (t-u)) u := by
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : u ∈ Icc 0 t
      · exact (indicator_of_mem hu (fun u => f u * g (t-u))).symm
      · rw [indicator_of_notMem hu]
        by_cases hu0 : u < 0
        · rw [hf u hu0, zero_mul]
        · rw [hg (t-u) (by
            have hut : t < u := by
              by_contra h
              exact hu ⟨le_of_not_gt hu0, le_of_not_gt h⟩
            linarith), mul_zero]
    _ = ∫ u in Icc 0 t, f u * g (t-u) := integral_indicator measurableSet_Icc
    _ = causal f g t := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
      rfl

private lemma cut_convolution {f g : ℝ → ℂ} {T t : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    convolution (cut T f) (cut T g) cmul volume t = causal f g t := by
  rw [convolution_of_causal (fun _ hx => cut_negative f T hx)
    (fun _ hx => cut_negative g T hx) ht]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  have hv : t-u ∈ Icc 0 T := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  simp only [cut, indicator_of_mem (show u ∈ Icc 0 T from ⟨hu.1, hu.2.trans htT⟩), indicator_of_mem hv]

/-- Finite associativity used only for the literal exponential/a/h below.
The two ae-existence premises and the full product-space integrability premise
of convolution_assoc' are supplied here, rather than assumed by a wrapper. -/
private lemma finite_assoc {f g k : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) (hk : Measurable k) {T Mf Mg Mk : ℝ}
    (hT : 0 ≤ T) (hMk : 0 ≤ Mk)
    (bf : ∀ u ∈ Icc 0 T, ‖f u‖ ≤ Mf)
    (bg : ∀ u ∈ Icc 0 T, ‖g u‖ ≤ Mg)
    (bk : ∀ u ∈ Icc 0 T, ‖k u‖ ≤ Mk) :
    causal (fun u => causal f g u) k T = causal f (fun u => causal g k u) T := by
  let F := cut T f
  let G := cut T g
  let H := cut T k
  have iF : Integrable F := cut_integrable hf bf
  have iG : Integrable G := cut_integrable hg bg
  have iH : Integrable H := cut_integrable hk bk
  have mH : Measurable H := hk.indicator measurableSet_Icc
  have bH (u : ℝ) : ‖H u‖ ≤ Mk := cut_bound hMk bk u
  have hfg : ∀ᵐ y : ℝ, ConvolutionExistsAt F G y cmul volume :=
    iF.ae_convolution_exists cmul iG
  have hgk : ∀ᵐ x : ℝ, ConvolutionExistsAt G H x cmul volume :=
    iG.ae_convolution_exists cmul iH
  have hpair : Integrable (fun p : ℝ × ℝ => F p.2 * G (p.1-p.2))
      (volume.prod volume) := iF.convolution_integrand cmul iG
  have hi : Integrable
      (Function.uncurry (fun x y : ℝ => F y * (G (x-y) * H (T-x))))
      (volume.prod volume) := by
    have hm : Measurable (fun p : ℝ × ℝ => H (T-p.1)) :=
      mH.comp (measurable_const.sub measurable_fst)
    have h := hpair.mul_bdd hm.aestronglyMeasurable (ae_of_all _ (fun p => bH (T-p.1)))
    simpa only [Function.uncurry_def, mul_assoc] using h
  have ha := convolution_assoc' cmul cmul cmul cmul
    (fun x y z => mul_assoc x y z) hfg hgk hi
  have nF : ∀ u < 0, F u = 0 := fun _ hu => cut_negative f T hu
  have nG : ∀ u < 0, G u = 0 := fun _ hu => cut_negative g T hu
  have nH : ∀ u < 0, H u = 0 := fun _ hu => cut_negative k T hu
  have left : convolution (convolution F G cmul volume) H cmul volume T =
      causal (fun u => causal f g u) k T := by
    rw [convolution_of_causal (fun _ hu => convolution_negative nF nG hu) nH hT]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT] at hu
    dsimp only
    rw [show convolution F G cmul volume u = causal f g u from cut_convolution hu.1 hu.2]
    simp only [H, cut, indicator_of_mem (show T-u ∈ Icc 0 T by constructor <;> linarith [hu.1, hu.2])]
  have right : convolution F (convolution G H cmul volume) cmul volume T =
      causal f (fun u => causal g k u) T := by
    rw [convolution_of_causal nF (fun _ hu => convolution_negative nG nH hu) hT]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT] at hu
    dsimp only
    rw [show convolution G H cmul volume (T-u) = causal g k (T-u) from
      cut_convolution (by linarith [hu.2]) (by linarith [hu.1])]
    simp only [F, cut, indicator_of_mem hu]
  exact left.symm.trans (ha.trans right)

private def ex (rho : ℂ) (t : ℝ) : ℂ := Complex.exp (lambda rho * (t : ℂ))

private lemma ex_a_eq_q (rho : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    causal (ex rho) aC t = q rho t := by
  rw [q, CausalResolventL1.q_eq_primitive aC (lambda rho) ht]
  have hc := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => ex rho (t-u) * aC u) t (a := (0 : ℝ)) (b := t)
  simp only [sub_self, sub_zero, sub_sub_cancel] at hc
  change (∫ u in (0 : ℝ)..t, ex rho u * aC (t-u)) = _
  rw [hc]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [ex]
  calc
    _ = aC u * Complex.exp (lambda rho * ((t-u : ℝ) : ℂ)) := by ring
    _ = aC u * (Complex.exp (lambda rho*(t : ℂ)) *
        Complex.exp (-lambda rho*(u : ℂ))) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = _ := by ring

private lemma actual_a_h {t : ℝ} (ht : 0 ≤ t) :
    causal aC hC t = (t : ℂ)*Complex.exp (-(t : ℂ)/2) := by
  change (∫ u in (0 : ℝ)..t,
    (MobiusCausalKernel.a u : ℂ) * (MobiusCausalKernel.h (t-u) : ℂ)) = _
  simp only [← Complex.ofReal_mul, intervalIntegral.integral_ofReal]
  rw [MobiusCausalKernel.causal_identity ht]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_ofNat]

private lemma exponential_local_bound (rho : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ‖ex rho t‖ ≤ M := by
  have hc : Continuous (ex rho) := by unfold ex; fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc.norm.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM (mem_image_of_mem _ ht)).trans (le_max_left _ _)

private lemma elementary_response {rho : ℂ} (hr : rho ≠ 0) (t : ℝ) :
    causal (ex rho) (fun u => (u : ℂ)*Complex.exp (-(u : ℂ)/2)) t =
      explicitOutput rho t := by
  let P : ℝ → ℂ := fun u => -(1+rho*(u : ℂ))*Complex.exp (-rho*(u : ℂ))/rho^2
  have hd (u : ℝ) : HasDerivAt P ((u : ℂ)*Complex.exp (-rho*(u : ℂ))) u := by
    have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    change HasDerivAt (fun u : ℝ =>
      -(1+rho*(u : ℂ))*Complex.exp (-rho*(u : ℂ))/rho^2) _ u
    convert (((((hid.const_mul rho).const_add 1).mul
      ((hid.const_mul (-rho)).cexp)).neg).div_const (rho^2)) using 1
    · funext v
      dsimp only [Pi.neg_apply, Pi.mul_apply]
      ring
    · field_simp [hr] <;> ring
  have hint : IntervalIntegrable (fun u : ℝ => (u : ℂ)*Complex.exp (-rho*(u : ℂ))) volume 0 t :=
    (by fun_prop : Continuous (fun u : ℝ => (u : ℂ)*Complex.exp (-rho*(u : ℂ)))).intervalIntegrable 0 t
  have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hint
  have hre : causal (ex rho) (fun u => (u : ℂ)*Complex.exp (-(u : ℂ)/2)) t =
      ex rho t * ∫ u in (0 : ℝ)..t, (u : ℂ)*Complex.exp (-rho*(u : ℂ)) := by
    have hs := intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => ex rho (t-u) * ((u : ℂ)*Complex.exp (-(u : ℂ)/2))) t
      (a := (0 : ℝ)) (b := t)
    simp only [sub_self, sub_zero, sub_sub_cancel] at hs
    rw [causal, hs, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp [ex, lambda]
    calc
      _ = (u : ℂ) * (Complex.exp ((rho-1/2)*((t-u : ℝ) : ℂ)) *
          Complex.exp (-(u : ℂ)/2)) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        have hh : (rho-1/2)*((t-u : ℝ) : ℂ) - (u : ℂ)/2 =
            (rho-1/2)*(t : ℂ) + (-rho*(u : ℂ)) := by push_cast; ring
        rw [show (rho-1/2)*((t-u : ℝ) : ℂ) + -(u : ℂ)/2 =
            (rho-1/2)*(t : ℂ) + (-rho*(u : ℂ)) by linear_combination hh]
        rw [Complex.exp_add]
        ring
  rw [hre, hev]
  have hexp : ex rho t * Complex.exp (-rho*(t : ℂ)) = Complex.exp (-(t : ℂ)/2) := by
    rw [ex, ← Complex.exp_add]
    congr 1
    dsimp [lambda]
    ring
  dsimp [ex, P, explicitOutput] at hexp ⊢
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, mul_one]
  field_simp [hr]
  simp only [neg_div, neg_mul, mul_comm (t : ℂ) rho] at hexp ⊢
  linear_combination -(1+rho*(t : ℂ))*hexp

/-- Actual finite integrability and exact output at EVERY nonnegative time.
The only zero-transform input is for a, supplied by MobiusKernelLaplace. -/
theorem response_integrable_and_eq {rho : ℂ} (hh : (1/2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => q rho u * hC (t-u)) volume 0 t ∧
    response rho t = explicitOutput rho t := by
  have hi : IntervalIntegrable (fun u => q rho u * hC (t-u)) volume 0 t := by
    apply bounded_interval ((q_measurable hh).mul
      (hC_measurable.comp (measurable_const.sub measurable_id))) ht
      (M := (2*t+6)*Real.exp (t/2))
    intro u hu
    change ‖q rho u * hC (t-u)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (q_local_bound hh hl hz hu)
      (hC_local_bound ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      (norm_nonneg _) (by linarith [ht])
  obtain ⟨M, hM, hb⟩ := exponential_local_bound rho ht
  have ha := finite_assoc (by unfold ex; fun_prop) aC_measurable hC_measurable
    ht (Real.exp_pos (t/2)).le hb (fun _ hu => aC_local_bound hu)
    (fun _ hu => hC_local_bound hu)
  refine ⟨hi, ?_⟩
  calc
    response rho t = causal (fun u => causal (ex rho) aC u) hC t := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht] at hu
      dsimp only
      rw [ex_a_eq_q rho hu.1]
    _ = causal (ex rho) (fun u => causal aC hC u) t := ha
    _ = causal (ex rho) (fun u => (u : ℂ)*Complex.exp (-(u : ℂ)/2)) t := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht] at hu
      dsimp only
      rw [actual_a_h (by linarith [hu.2] : 0 ≤ t-u)]
    _ = explicitOutput rho t := elementary_response (rho_ne_zero hh) t



lemma cut_prefix_transfer {rho : ℂ} (hh : (1 / 2 : ℝ) ≤ rho.re)
    (hl : rho.re < 1) (hz : riemannZeta rho = 0) {T M : ℝ} (hT : 0 ≤ T)
    {f : ℝ → ℂ} (hf : Measurable f) (hb : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) :
    IntervalIntegrable (fun t => ‖causal (q rho) f t‖^2) volume 0 T ∧
    (∫ t in (0 : ℝ)..T, ‖causal (q rho) f t‖^2) ≤
      400 * ∫ t in (0 : ℝ)..T, ‖f t‖^2 := by
  let F := cut T f
  have mF : Measurable F := hf.indicator measurableSet_Icc
  have hsq : (fun t => ‖F t‖^2) = cut T (fun t => ‖f t‖^2) := by
    funext t
    by_cases ht : t ∈ Icc 0 T
    · simp [F, cut, ht]
    · simp [F, cut, ht]
  have iF2 : Integrable (fun t => ‖F t‖^2) := by
    rw [hsq]
    apply cut_integrable (M := M^2) (hf.norm.pow_const 2)
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb t ht) 2
  have lF : MemLp F 2 := (memLp_two_iff_integrable_sq_norm mF.aestronglyMeasurable).mpr iF2
  have hy := D5.S3.Analytic.Fourier.ConvolutionL2.convolution_memLp_two
    (q_budget hh hl hz).1 lF
  let V := D5.S3.Analytic.Fourier.ConvolutionL2.conv (q rho) F
  have iV2 : Integrable (fun t => ‖V t‖^2) :=
    (memLp_two_iff_integrable_sq_norm hy.1.aestronglyMeasurable).mp hy.1
  have hv (t : ℝ) (ht : t ∈ Icc 0 T) : V t = causal (q rho) f t := by
    change convolution (q rho) F cmul volume t = _
    rw [convolution_of_causal (f := q rho) (g := F)
      (fun _ hx => CausalResolventL1.q_eq_zero_of_neg aC (lambda rho) hx)
      (fun _ hx => cut_negative f T hx) ht.1]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp only
    rw [show F (t-u) = f (t-u) from
      indicator_of_mem (show t-u ∈ Icc 0 T by constructor <;> linarith [hu.1, hu.2, ht.2]) f]
  have hbound : (eLpNorm V 2).toReal ≤ 20 * (eLpNorm F 2).toReal := by
    have hb := hy.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (q_budget hh hl hz).2) le_rfl)
    have hb' := ENNReal.toReal_mono (by finiteness) hb
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 20)] using hb'
  have hglobal : (∫ t : ℝ, ‖V t‖^2) ≤ 400 * ∫ t in (0 : ℝ)..T, ‖f t‖^2 := by
    have hb' := pow_le_pow_left₀ ENNReal.toReal_nonneg hbound 2
    rw [mul_pow, ← complex_l2_integral hy.1, ← complex_l2_integral lF] at hb'
    have hinput : (∫ t : ℝ, ‖F t‖^2) = ∫ t in (0 : ℝ)..T, ‖f t‖^2 := by
      rw [hsq, cut, integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
    simpa only [hinput, show (20 : ℝ)^2 = 400 by norm_num] using hb'
  refine ⟨?_, ?_⟩
  · apply iV2.intervalIntegrable.congr
    intro t ht
    rw [uIoc_of_le hT] at ht
    dsimp only
    rw [hv t ⟨ht.1.le, ht.2⟩]
  calc
    _ = ∫ t in (0 : ℝ)..T, ‖V t‖^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      dsimp only
      rw [hv t ht]
    _ ≤ ∫ t : ℝ, ‖V t‖^2 := by
      rw [intervalIntegral.integral_of_le hT]
      exact setIntegral_le_integral iV2 (ae_of_all _ (fun t => sq_nonneg ‖V t‖))
    _ ≤ _ := hglobal


def lead (rho : ℂ) (t : ℝ) : ℂ := Complex.exp (lambda rho*(t : ℂ))

lemma lead_norm_sq (rho : ℂ) (t : ℝ) :
    ‖lead rho t‖^2 = Real.exp ((2*rho.re-1)*t) := by
  have hn : ‖lead rho t‖ = Real.exp ((rho.re-1/2)*t) := by
    simp [lead, lambda, Complex.norm_exp]
  rw [hn, pow_two, ← Real.exp_add]
  congr 1
  ring

end MobiusCausalPrefixEnergy
