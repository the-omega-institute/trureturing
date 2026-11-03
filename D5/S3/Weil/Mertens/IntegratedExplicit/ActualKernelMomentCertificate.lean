/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full actual-K endpoint certificate and finite signed expression. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact scalar order arithmetic for the actual moment endpoint. -/

namespace ActualKScalarSource

noncomputable section

open Filter Topology Real

variable (C alpha D : ℝ)

private def factorial10 : ℝ := (Nat.factorial 10 : ℝ)

def B : ℝ := C * (1 + factorial10 * (2 / alpha) ^ (10 : ℕ))

def d0 : ℝ := Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)

def M : ℝ := Real.exp (D / 2)

def beta : ℝ :=
  M D * (1 + C * (Real.exp (-alpha * (D / 4) ^ (1 / 10 : ℝ)) +
    Real.exp (-D / 4))) + D + B C alpha

def curvature : ℝ :=
  ((9 + 4 * C + 2 * B C alpha) * M D + D + 3) / 4

def N : ℕ := Nat.ceil (max 1 (max (D * Real.sqrt (curvature C alpha D) / 2)
  ((5 * D / 4) * Real.exp (beta C alpha D + d0 + 2))))

def delta (D : ℝ) (q : ℕ) : ℝ := D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))

theorem B_ge_C (hC : 1 ≤ C) : C ≤ B C alpha := by
  have h : 0 ≤ factorial10 * (2 / alpha) ^ (10 : ℕ) := by
    unfold factorial10
    positivity
  unfold B
  nlinarith

theorem B_ge_one (hC : 1 ≤ C) : 1 ≤ B C alpha :=
  hC.trans (B_ge_C C alpha hC)

theorem one_le_M (hD : 0 < D) : 1 ≤ M D := by
  exact Real.one_le_exp (by positivity)

theorem base_lt_beta (hC : 1 ≤ C) : M D + D + B C alpha < beta C alpha D := by
  have hm : 0 < M D := Real.exp_pos _
  have he : 0 < C * (Real.exp (-alpha * (D / 4) ^ (1 / 10 : ℝ)) +
      Real.exp (-D / 4)) := mul_pos (by linarith) (add_pos (Real.exp_pos _) (Real.exp_pos _))
  unfold beta
  nlinarith [mul_pos hm he]

theorem two_le_beta (hC : 1 ≤ C) (hD : 0 < D) : 2 ≤ beta C alpha D := by
  have := base_lt_beta C alpha D hC
  have := B_ge_one C alpha hC
  have := one_le_M D hD
  linarith

theorem d0_nonneg : 0 ≤ d0 := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have hl := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 5 by norm_num)
  have hp : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 6) hp
  norm_num at hl
  unfold d0
  linarith

theorem curvature_lt_two_beta_sq (hC : 1 ≤ C) (hD : 0 < D) :
    curvature C alpha D < 2 * (beta C alpha D) ^ 2 := by
  have hB := B_ge_one C alpha hC
  have hBC := B_ge_C C alpha hC
  have hM := one_le_M D hD
  have hbeta := base_lt_beta C alpha D hC
  have hS : 0 < M D + D + B C alpha := by linarith
  have hsq : (M D + D + B C alpha) ^ 2 < (beta C alpha D) ^ 2 := by
    nlinarith
  have h1 : 0 < M D * (8 * M D + 10 * B C alpha - 9) := by
    apply mul_pos <;> linarith
  have h2 : 0 ≤ 4 * M D * (B C alpha - C) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hBC)
  have h3 : 0 < 8 * (B C alpha) ^ 2 - 3 := by nlinarith
  have h4 : 0 ≤ D * (16 * M D - 1) := mul_nonneg hD.le (by linarith)
  have h5 : 0 ≤ 16 * B C alpha * D := by positivity
  have hexpand :
      8 * (M D + D + B C alpha) ^ 2 -
          ((9 + 4 * C + 2 * B C alpha) * M D + D + 3) =
        M D * (8 * M D + 10 * B C alpha - 9) +
          4 * M D * (B C alpha - C) + (8 * (B C alpha) ^ 2 - 3) +
          D * (16 * M D - 1) + 8 * D ^ 2 + 16 * B C alpha * D := by ring
  unfold curvature
  nlinarith [sq_nonneg D]

theorem eight_beta_le_exp (hC : 1 ≤ C) (hD : 0 < D) :
    8 * beta C alpha D ≤ Real.exp (beta C alpha D + d0 + 2) := by
  have hb := two_le_beta C alpha D hC hD
  have he := Real.two_mul_le_exp (x := beta C alpha D)
  have he2 := Real.two_mul_le_exp (x := (2 : ℝ))
  have hd : Real.exp 2 ≤ Real.exp (d0 + 2) := Real.exp_le_exp.mpr (by
    linarith [d0_nonneg])
  have hp := mul_le_mul he (show 4 ≤ Real.exp (d0 + 2) by linarith)
    (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_pos _).le
  rw [show beta C alpha D + d0 + 2 = beta C alpha D + (d0 + 2) by ring,
    Real.exp_add]
  nlinarith

theorem third_term_le_N :
    (5 * D / 4) * Real.exp (beta C alpha D + d0 + 2) ≤ (N C alpha D : ℝ) := by
  exact (le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))

theorem one_le_N : 1 ≤ N C alpha D := by
  apply Nat.one_le_ceil_iff.mpr
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)

theorem ten_D_beta_le_N (hC : 1 ≤ C) (hD : 0 < D) :
    10 * D * beta C alpha D ≤ (N C alpha D : ℝ) := by
  have he := eight_beta_le_exp C alpha D hC hD
  have h := mul_le_mul_of_nonneg_left he (show 0 ≤ 5 * D / 4 by positivity)
  have hN := third_term_le_N C alpha D
  nlinarith

theorem log_five_fourths : (1 : ℝ) / 5 ≤ Real.log (5 / 4) := by
  have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  norm_num at h ⊢
  linarith

theorem q_log_lower (hD : 0 < D) :
    beta C alpha D + d0 + 2 + Real.log (5 / 4) ≤
      Real.log ((N C alpha D : ℝ) / D) := by
  have ht : (5 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2) ≤
      (N C alpha D : ℝ) / D := by
    apply (le_div_iff₀ hD).mpr
    nlinarith [third_term_le_N C alpha D]
  have hl := Real.log_le_log (by positivity :
    0 < (5 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2)) ht
  rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hl
  linarith

theorem q_delta_bound (hC : 1 ≤ C) (hD : 0 < D) :
    delta D (N C alpha D) * curvature C alpha D ≤ (1 : ℝ) / 200 := by
  have hb := two_le_beta C alpha D hC hD
  have hN := ten_D_beta_le_N C alpha D hC hD
  have hq : 0 < (N C alpha D : ℝ) := by
    exact_mod_cast (show 0 < N C alpha D from lt_of_lt_of_le Nat.zero_lt_one (one_le_N C alpha D))
  have hs : (10 * D * beta C alpha D) ^ 2 ≤ (N C alpha D : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hq.le).2 hN
  have hc := mul_le_mul_of_nonneg_left
    (curvature_lt_two_beta_sq C alpha D hC hD).le (sq_nonneg D)
  have hd : 0 < 4 * (N C alpha D : ℝ) * ((N C alpha D : ℝ) + 1) := by positivity
  unfold delta
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  nlinarith

theorem q_scalar_bounds (hC : 1 ≤ C) (hD : 0 < D) :
    1 ≤ N C alpha D ∧
      (8 : ℝ) ≤ (N C alpha D : ℝ) / D ∧
      delta D (N C alpha D) * curvature C alpha D ≤ (1 : ℝ) / 8 ∧
      beta C alpha D + d0 + 2 + (1 : ℝ) / 5 ≤
        Real.log ((N C alpha D : ℝ) / D) := by
  refine ⟨one_le_N C alpha D, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hD).mpr
    have := ten_D_beta_le_N C alpha D hC hD
    have := two_le_beta C alpha D hC hD
    nlinarith
  · exact (q_delta_bound C alpha D hC hD).trans (by norm_num)
  · linarith [q_log_lower C alpha D hD, log_five_fourths]

#print axioms q_scalar_bounds

end
end ActualKScalarSource
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
