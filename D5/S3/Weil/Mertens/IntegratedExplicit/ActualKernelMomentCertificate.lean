/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full actual-K endpoint certificate and finite signed expression. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualMomentOrderArithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

private lemma d0_nonneg : 0 ≤ d0 :=
  ActualKScalarSource.d0_nonneg

/-- Full original remainder, with every H/V/b(D) correction paid. -/
private theorem actual_remainder_prefix_bound_leading_one (p : PNTConstants)
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (quadratic x a P).re -
      (d0 + beta p D + D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * curvature p D) * energy x a ≤
        (quadratic x a ActualKernelLocalPositivity.K).re := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hT := actual_weighted_mangoldt_translation_bound p D x a hx ha
  have hR := actual_fullR_correlation D hD.le x a hx ha
  have hV := actual_fullR_resolvent_identity D hD.le x a ha
  have hS := actual_resolvent_control D hD q hq x a hx hm
  have hH := actual_continuum_moment_payment D hD q hq x a hx hm
  have hcut := actual_cutoff_resolvent_payment p D hD x a hx ha
  have hcoeff : 0 ≤ (8 + 4 * p.C + 2 * B p) * M D := by
    have hb := p.one_le_C.trans (B_ge_C p)
    have hC := p.one_le_C
    exact mul_nonneg (by linarith) (Real.exp_nonneg _)
  have hVlower : -((8 + 4 * p.C + 2 * B p) * M D *
      (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a / 4) ≤ V D x a := by
    have h := mul_le_mul_of_nonneg_left hS.2.2.1 hcoeff
    have hl := (abs_le.mp hcut).1
    nlinarith only [h, hl]
  have hdW : 0 ≤ d0 * W D x a := mul_nonneg d0_nonneg hS.1
  have hsplit : (quadratic x a ActualKernelLocalPositivity.K).re =
      (quadratic x a P).re + (quadratic x a fullR).re := by
    simp only [quadratic, original_K_split, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib, Complex.add_re]
  dsimp only [curvature]
  nlinarith only [hT, hR, hV, hH, hVlower, hdW, hsplit]

/-- Exact arithmetic supplied by the compiled scalar owner at the same ceiling. -/
private theorem original_order_arithmetic (p : PNTConstants) (D : ℝ) (hD : 0 < D) :
    1 ≤ order p D ∧ 8 ≤ (order p D : ℝ) / D ∧
      D ^ 2 / (4 * (order p D : ℝ) * ((order p D : ℝ) + 1)) * curvature p D ≤ (1 / 8 : ℝ) ∧
        beta p D + d0 + 2 + 1 / 5 ≤ Real.log ((order p D : ℝ) / D) := by
  exact ActualKScalarSource.q_scalar_bounds p.C p.alpha D p.one_le_C hD

/-- The original actual-K certificate at exactly the displayed N(D).
The fixed unconditional pnt witnesses precede every finite atomic family.
Atomic moments include degree N. No distinctness, nonempty type,
positive-energy or real-coefficient restriction occurs. -/
theorem actual_kernel_explicit_leading_one (D : ℝ) (hD : 0 < D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ order pnt D → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    energy x a ≤ (quadratic x a ActualKernelLocalPositivity.K).re := by
  have hq := original_order_arithmetic pnt D hD
  have hP := complete_positive_mixture_logarithmic
    D hD (order pnt D) hq.1 hq.2.1 x a hx hm
  have hR := actual_remainder_prefix_bound_leading_one
    pnt D hD (order pnt D) hq.1 x a hx hm
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  have hlog := mul_le_mul_of_nonneg_right hq.2.2.2 hE
  have hpay := mul_le_mul_of_nonneg_right hq.2.2.1 hE
  nlinarith only [hP, hR, hlog, hpay, hE]

/-- Compensation for the explicitly defined finite formula only. Equality
with an independently defined original signed-J integral is an additional,
separate obligation and is not assumed or asserted here. -/
theorem actual_signed_expression_compensation (D : ℝ) (hD : 0 < D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ order pnt D → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (Real.log (2 * Real.pi) - 1 - Real.eulerMascheroniConstant) *
      (energy x a - W D x a) - (quadratic x a P).re + energy x a ≤ signedJExpression D x a := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le _)
  have hK := actual_kernel_explicit_leading_one D hD x a hx hm
  have hR := actual_fullR_correlation D hD.le x a hx ha
  have hV := actual_fullR_resolvent_identity D hD.le x a ha
  have hsplit : (quadratic x a ActualKernelLocalPositivity.K).re =
      (quadratic x a P).re + (quadratic x a fullR).re := by
    simp only [quadratic, original_K_split, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib, Complex.add_re]
  dsimp only [signedJExpression, d0] at *
  linarith only [hK, hR, hV, hsplit]


end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
