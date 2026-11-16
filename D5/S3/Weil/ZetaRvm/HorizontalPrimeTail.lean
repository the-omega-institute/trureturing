/- GID: D5/S3/Weil/ZetaRvm/HorizontalPrimeTail
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaRvm/HorizontalPrimeTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute prime Fourier expansion of the actual horizontal zeta tail. -/

import D5.S3.Weil.ZetaRvm.HorizontalLogTail
import D5.S3.Weil.ZetaExplicit.XiLogDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual horizontal zeta tail as a prime Fourier series

The verified von Mangoldt L-series identity supplies the logarithmic derivative.
A local derivative of the genuine principal logarithm and its limit at infinity
identify the actual lognorm. Two integrations, each with its own summable L¹
majorant, yield the coefficient Λ(n)/(n^R log(n)^2). Total real division retains
both n = 0 and n = 1 as zero terms. The result includes R = 2 and every real t.
It identifies Littlewood's right-boundary tail; the central RH sign `E ≤ 0`
remains unproved.

The cpow calculation in `lseries_term_horizontal` adapts
`Zeta23.WeilEF.per_n_line_integral` in
`D5/S3/Weil/ZetaExplicit/VerticalLine.lean`, ported from
`anthropics/zeta-23-lean` commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, copyright Anthropic PBC,
Apache-2.0. Logarithmic-derivative and summability suppliers are Mathlib's
`ArithmeticFunction` declarations. No Euler logarithm identity is assumed.
-/

noncomputable section

open Complex Set Filter MeasureTheory
open scoped Topology Interval

namespace Zeta23.RvM

/-- The actual prime-power coefficient, using total real division at 0 and 1. -/
def zetaHorizontalPrimeCoeff (R : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n /
    ((n : ℝ) ^ R * (Real.log (n : ℝ)) ^ 2)

private def weight (k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n /
    ((n : ℝ) ^ σ * (Real.log (n : ℝ)) ^ k)

private def primeTerm (k : ℕ) (σ t : ℝ) (n : ℕ) : ℝ :=
  weight k σ n * Real.cos (t * Real.log (n : ℝ))

private def negLogDerivRe (σ t : ℝ) : ℝ :=
  (-logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re

@[simp] private lemma weight_zero (k : ℕ) (σ : ℝ) : weight k σ 0 = 0 := by
  simp [weight]

@[simp] private lemma weight_one (k : ℕ) (σ : ℝ) : weight k σ 1 = 0 := by
  simp [weight, ArithmeticFunction.vonMangoldt_apply_one]

@[simp] private lemma primeTerm_zero (k : ℕ) (σ t : ℝ) :
    primeTerm k σ t 0 = 0 := by simp [primeTerm]

@[simp] private lemma primeTerm_one (k : ℕ) (σ t : ℝ) :
    primeTerm k σ t 1 = 0 := by simp [primeTerm]

private lemma nat_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < (n : ℝ) := by
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private lemma log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  apply Real.log_pos
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private lemma weight_nonneg (k : ℕ) (σ : ℝ) (n : ℕ) : 0 ≤ weight k σ n := by
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (Real.log_natCast_nonneg n) k))

private lemma summable_weight_zero {R : ℝ} (hR : 1 < R) :
    Summable (weight 0 R) := by
  have hs : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (R : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hR)
  have hns : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (R : ℂ) n‖) :=
    summable_norm_iff.mpr hs
  refine hns.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weight, LSeries.term_zero]
  · rw [LSeries.norm_term_eq, if_neg hn]
    simp [weight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

private lemma weight_le_base (k : ℕ) (R : ℝ) (n : ℕ) :
    weight k R n ≤ weight 0 R n * ((Real.log 2) ^ k)⁻¹ := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hn0 := nat_pos_of_two_le hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) hn2
    have hp : (Real.log 2) ^ k ≤ (Real.log (n : ℝ)) ^ k :=
      pow_le_pow_left₀ (Real.log_pos (by norm_num) : 0 < Real.log 2).le hlog k
    have hd : 0 < (n : ℝ) ^ R * (Real.log 2) ^ k :=
      mul_pos (Real.rpow_pos_of_pos hn0 R) (pow_pos (Real.log_pos (by norm_num) : 0 < Real.log 2) k)
    calc
      weight k R n ≤ ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ R * (Real.log 2) ^ k) := by
        exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hd
          (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hn0.le _))
      _ = weight 0 R n * ((Real.log 2) ^ k)⁻¹ := by
        simp [weight, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

private lemma summable_weight (k : ℕ) {R : ℝ} (hR : 1 < R) :
    Summable (weight k R) :=
  Summable.of_nonneg_of_le (weight_nonneg k R) (weight_le_base k R)
    ((summable_weight_zero hR).mul_right _)

private lemma norm_primeTerm (k : ℕ) (σ t : ℝ) (n : ℕ) :
    ‖primeTerm k σ t n‖ = weight k σ n * |Real.cos (t * Real.log (n : ℝ))| := by
  simp [primeTerm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg k σ n)]

private lemma norm_primeTerm_le (k : ℕ) (σ t : ℝ) (n : ℕ) :
    ‖primeTerm k σ t n‖ ≤ weight k σ n := by
  rw [norm_primeTerm]
  simpa using mul_le_mul_of_nonneg_left
    (Real.abs_cos_le_one (t * Real.log (n : ℝ))) (weight_nonneg k σ n)

private lemma summable_norm_primeTerm (k : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n : ℕ => ‖primeTerm k σ t n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_primeTerm_le k σ t)
    (summable_weight k hσ)

-- This is the per-index calculation in VerticalLine.per_n_line_integral,
-- without its Fourier test function. The n=0 branch uses the actual term_zero.
private lemma lseries_term_horizontal (σ t : ℝ) (n : ℕ) :
    (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((σ : ℂ) + (t : ℂ) * I) n).re = primeTerm 0 σ t n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hterm : LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t : ℂ) * I) n =
        (ArithmeticFunction.vonMangoldt n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.exp (-I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
      have hsplit : (-((σ : ℂ) + (t : ℂ) * I)) = (-(σ : ℂ)) + (-(I * (t : ℂ))) := by
        ring
      rw [hsplit, Complex.cpow_add _ _ hnC]
      have h1 : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        rw [show (n : ℂ) = (((n : ℝ) : ℂ)) by push_cast; rfl,
          show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow hn0.le]
      have h2 : (n : ℂ) ^ (-(I * (t : ℂ))) =
          Complex.exp (-I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hnC]
        congr 1
        rw [show (n : ℂ) = (((n : ℝ) : ℂ)) by push_cast; rfl,
          ← Complex.ofReal_log hn0.le]
        ring
      rw [h1, h2]
      ring
    rw [hterm]
    have he : -I * (t : ℂ) * (Real.log (n : ℝ) : ℂ) =
        (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ)) * I := by push_cast; ring
    rw [he]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, zero_add, add_zero, sub_zero, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
      primeTerm, weight, pow_zero, mul_one, Real.rpow_neg hn0.le, div_eq_mul_inv]

private lemma negLogDerivRe_eq_tsum {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    negLogDerivRe σ t = ∑' n : ℕ, primeTerm 0 σ t n := by
  have hre : 1 < ((σ : ℂ) + (t : ℂ) * I).re := by simpa using hσ
  have he : -logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    rw [logDeriv, Pi.div_apply, h]
    ring
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt hre
  unfold negLogDerivRe
  rw [he]
  change (∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
    ((σ : ℂ) + (t : ℂ) * I) n).re = _
  rw [Complex.re_tsum hs]
  exact tsum_congr (lseries_term_horizontal σ t)

-- Each term is one decaying real exponential with a constant, for every t.
private lemma weight_eq_exp (k : ℕ) {n : ℕ} (hn : 2 ≤ n) (σ : ℝ) :
    weight k σ n = (ArithmeticFunction.vonMangoldt n / (Real.log (n : ℝ)) ^ k) *
      Real.exp ((-Real.log (n : ℝ)) * σ) := by
  unfold weight
  rw [Real.rpow_def_of_pos (nat_pos_of_two_le hn)]
  rw [show Real.log (n : ℝ) * σ = -((-Real.log (n : ℝ)) * σ) by ring]
  simp [Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

private lemma primeTerm_eq_exp (k : ℕ) {n : ℕ} (hn : 2 ≤ n) (σ t : ℝ) :
    primeTerm k σ t n =
      (ArithmeticFunction.vonMangoldt n / (Real.log (n : ℝ)) ^ k *
        Real.cos (t * Real.log (n : ℝ))) * Real.exp ((-Real.log (n : ℝ)) * σ) := by
  rw [primeTerm, weight_eq_exp k hn]
  ring

private lemma integrableOn_primeTerm (k : ℕ) (R t : ℝ) (n : ℕ) :
    IntegrableOn (fun σ : ℝ => primeTerm k σ t n) (Ioi R) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simpa using (integrable_zero : IntegrableOn (0 : ℝ → ℝ) (Ioi R))
  · simp_rw [primeTerm_eq_exp k hn]
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (log_pos_of_two_le hn)) R).const_mul _

private lemma integral_primeTerm (k : ℕ) (R t : ℝ) (n : ℕ) :
    (∫ σ : ℝ in Ioi R, primeTerm k σ t n) = primeTerm (k + 1) R t n := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hl : 0 < Real.log (n : ℝ) := log_pos_of_two_le hn
    simp_rw [primeTerm_eq_exp k hn]
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hl)]
    rw [primeTerm_eq_exp (k + 1) hn]
    simp only [neg_div_neg_eq, pow_succ]
    field_simp [ne_of_gt hl] <;> ring

-- The actual integral norms of ALL terms are summable. This is the bound
-- used in both swaps (k=0 and k=1), rather than a formal Fubini assertion.
private lemma summable_integral_norm_primeTerm (k : ℕ) {R : ℝ}
    (hR : 1 < R) (t : ℝ) :
    Summable (fun n : ℕ => ∫ σ : ℝ in Ioi R, ‖primeTerm k σ t n‖) := by
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg (fun σ => norm_nonneg _)) (fun n => ?_)
    (summable_weight (k + 1) hR)
  have hiw : IntegrableOn (fun σ : ℝ => weight k σ n) (Ioi R) := by
    simpa [primeTerm] using integrableOn_primeTerm k R 0 n
  have hew : (∫ σ : ℝ in Ioi R, weight k σ n) = weight (k + 1) R n := by
    simpa [primeTerm] using integral_primeTerm k R 0 n
  calc
    (∫ σ : ℝ in Ioi R, ‖primeTerm k σ t n‖) ≤
        ∫ σ : ℝ in Ioi R, weight k σ n :=
      integral_mono_ae (integrableOn_primeTerm k R t n).norm hiw
        (Eventually.of_forall fun σ => norm_primeTerm_le k σ t n)
    _ = weight (k + 1) R n := hew

private lemma weight_zero_decay {R σ : ℝ} (hRσ : R ≤ σ) (n : ℕ) :
    weight 0 σ n ≤ weight 0 R n * (2 : ℝ) ^ (R - σ) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hn0 := nat_pos_of_two_le hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have he : weight 0 σ n = weight 0 R n * (n : ℝ) ^ (R - σ) := by
      simp only [weight, pow_zero, mul_one]
      rw [Real.rpow_sub hn0]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hn0 R),
        ne_of_gt (Real.rpow_pos_of_pos hn0 σ)] <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith))
      (weight_nonneg 0 R n)

private lemma two_rpow_eq_exp (A σ : ℝ) :
    (2 : ℝ) ^ (A - σ) =
      Real.exp (A * Real.log 2) * Real.exp ((-Real.log 2) * σ) := by
  rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
  congr 1
  ring

private lemma integrableOn_two_majorant (K A R : ℝ) :
    IntegrableOn (fun σ : ℝ => K * (2 : ℝ) ^ (A - σ)) (Ioi R) := by
  have h := (integrableOn_exp_mul_Ioi (by linarith [(Real.log_pos (by norm_num) : 0 < Real.log 2)] : -Real.log 2 < 0)
    R).const_mul (K * Real.exp (A * Real.log 2))
  simpa only [IntegrableOn, two_rpow_eq_exp, mul_assoc] using h

private lemma norm_negLogDerivRe_le {R σ : ℝ} (hR : 2 ≤ R)
    (hRσ : R ≤ σ) (t : ℝ) :
    ‖negLogDerivRe σ t‖ ≤ (∑' n : ℕ, weight 0 R n) * (2 : ℝ) ^ (R - σ) := by
  have hσ : 1 < σ := by linarith
  have hR1 : 1 < R := by linarith
  rw [negLogDerivRe_eq_tsum hσ]
  calc
    ‖∑' n : ℕ, primeTerm 0 σ t n‖ ≤ ∑' n : ℕ, ‖primeTerm 0 σ t n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_primeTerm 0 hσ t)
    _ ≤ ∑' n : ℕ, weight 0 R n * (2 : ℝ) ^ (R - σ) :=
      (summable_norm_primeTerm 0 hσ t).tsum_le_tsum
        (fun n => (norm_primeTerm_le 0 σ t n).trans (weight_zero_decay hRσ n))
        ((summable_weight_zero hR1).mul_right _)
    _ = (∑' n : ℕ, weight 0 R n) * (2 : ℝ) ^ (R - σ) := by rw [tsum_mul_right]

private lemma horizontal_ne_one {σ : ℝ} (hσ : 2 ≤ σ) (t : ℝ) :
    (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
  intro he
  have hh := congrArg Complex.re he
  simp at hh
  linarith

private lemma continuousOn_negLogDerivRe {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    ContinuousOn (fun σ : ℝ => negLogDerivRe σ t) (Ici R) := by
  intro σ hσ
  have hs : 2 ≤ ((σ : ℂ) + (t : ℂ) * I).re := by simpa using hR.trans hσ
  have ha := Zeta23.WeilEF.analyticAt_riemannZeta (horizontal_ne_one (hR.trans hσ) t)
  have hz : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro he
    have hh := re_zeta_pos_of_two_le_re hs
    rw [he] at hh
    simpa using hh
  have hc : ContinuousAt (fun z : ℂ => (-logDeriv riemannZeta z).re)
      ((σ : ℂ) + (t : ℂ) * I) := by
    simpa only [logDeriv_apply, Function.comp_def, Pi.neg_apply, Pi.div_apply] using
      Complex.continuous_re.continuousAt.comp
        ((ha.deriv.continuousAt.div ha.continuousAt hz).neg)
  exact (hc.comp (f := fun x : ℝ => (x : ℂ) + (t : ℂ) * I)
    (by fun_prop)).continuousWithinAt

private lemma integrableOn_negLogDerivRe {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    IntegrableOn (fun σ : ℝ => negLogDerivRe σ t) (Ioi R) := by
  refine (integrableOn_two_majorant (∑' n : ℕ, weight 0 R n) R R).mono'
    (((continuousOn_negLogDerivRe hR t).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact norm_negLogDerivRe_le hR hσ.le t

-- Only local differentiation of the genuine principal log is used. Re ζ>0
-- puts ζ in its slit plane; Complex.log_re then gives the ACTUAL lognorm.
private lemma horizontal_log_norm_hasDerivAt {σ : ℝ} (hσ : 2 ≤ σ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖)
      (-negLogDerivRe σ t) σ := by
  have hs : 2 ≤ ((σ : ℂ) + (t : ℂ) * I).re := by simpa using hσ
  have hζ := (differentiableAt_riemannZeta (horizontal_ne_one hσ t)).hasDerivAt
  have hγ : HasDerivAt (fun z : ℂ => z + (t : ℂ) * I) 1 (σ : ℂ) :=
    (hasDerivAt_id _).add_const _
  have hlog := (Complex.hasDerivAt_log (Or.inl (re_zeta_pos_of_two_le_re hs))).comp (σ : ℂ)
    (hζ.comp (σ : ℂ) hγ)
  have hreal := hlog.real_of_complex
  simpa only [riemannZeta, Function.comp_def, negLogDerivRe, Complex.log_re, logDeriv_apply,
    mul_one, one_mul, Complex.neg_re, neg_neg, div_eq_mul_inv, mul_comm] using hreal

local notation "q" => (Real.pi ^ 2 / 6 - 1 : ℝ)
local notation "Ctail" => (q / (1 - q))

private lemma tendsto_two_decay :
    Tendsto (fun X : ℝ => (2 : ℝ) ^ (2 - X)) atTop (𝓝 0) := by
  have he : Tendsto (fun X : ℝ => Real.exp ((-Real.log 2) * X)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop
        (by linarith [(Real.log_pos (by norm_num) : 0 < Real.log 2)] : -Real.log 2 < 0) tendsto_id)
  simpa only [two_rpow_eq_exp, mul_zero] using he.const_mul (Real.exp (2 * Real.log 2))

private lemma tendsto_log_norm_zero (t : ℝ) :
    Tendsto (fun X : ℝ => Real.log ‖riemannZeta ((X : ℂ) + (t : ℂ) * I)‖)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun X : ℝ => Ctail * (2 : ℝ) ^ (2 - X))
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    have h := (Complex.abs_re_le_norm
      (Complex.log (riemannZeta ((X : ℂ) + (t : ℂ) * I)))).trans
        (norm_log_riemannZeta_le_rpow (by simpa using hX))
    simpa only [Complex.log_re, Real.norm_eq_abs, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using h
  · simpa only [mul_zero] using tendsto_two_decay.const_mul Ctail

private lemma integral_negLogDerivRe {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    (∫ σ : ℝ in Ioi R, negLogDerivRe σ t) =
      Real.log ‖riemannZeta ((R : ℂ) + (t : ℂ) * I)‖ := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun σ : ℝ => -Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
    (f' := fun σ : ℝ => negLogDerivRe σ t) (m := (0 : ℝ))
    (fun σ hσ => by
      have hd := (horizontal_log_norm_hasDerivAt (hR.trans hσ) t).neg
      rw [show -(fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) =
        (fun x : ℝ => -Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) from rfl] at hd
      simpa only [neg_neg] using hd)
    (integrableOn_negLogDerivRe hR t)
    (by simpa only [neg_zero] using (tendsto_log_norm_zero t).neg)
  simpa only [zero_sub, neg_neg] using h

-- The missing actual-zeta inference: one integral of the verified L-series
-- equals the genuine lognorm by FTC and the supplier's limit at infinity.
private lemma log_norm_eq_prime_tsum {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    Real.log ‖riemannZeta ((R : ℂ) + (t : ℂ) * I)‖ =
      ∑' n : ℕ, primeTerm 1 R t n := by
  have hR1 : 1 < R := by linarith
  calc
    Real.log ‖riemannZeta ((R : ℂ) + (t : ℂ) * I)‖ =
        ∫ σ : ℝ in Ioi R, negLogDerivRe σ t := (integral_negLogDerivRe hR t).symm
    _ = ∫ σ : ℝ in Ioi R, ∑' n : ℕ, primeTerm 0 σ t n := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro σ hσ
      exact negLogDerivRe_eq_tsum (lt_trans hR1 hσ) t
    _ = ∑' n : ℕ, ∫ σ : ℝ in Ioi R, primeTerm 0 σ t n :=
      (integral_tsum_of_summable_integral_norm
        (integrableOn_primeTerm 0 R t) (summable_integral_norm_primeTerm 0 hR1 t)).symm
    _ = ∑' n : ℕ, primeTerm 1 R t n :=
      tsum_congr (integral_primeTerm 0 R t)

/-- Absolute convergence of the actual coefficient and Fourier series, and
the exact prime realization of the actual horizontal tail. The endpoints
R=2 and t=0 and every negative real height are included in the telescope. -/
theorem zetaHorizontalLogTail_prime_expansion {R : ℝ} (hR : 2 ≤ R) (t : ℝ) :
    Summable (fun n : ℕ => |zetaHorizontalPrimeCoeff R n|) ∧
    Summable (fun n : ℕ =>
      |zetaHorizontalPrimeCoeff R n * Real.cos (t * Real.log (n : ℝ))|) ∧
    zetaHorizontalLogTail R t =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ R * (Real.log (n : ℝ)) ^ 2)) *
          Real.cos (t * Real.log (n : ℝ)) := by
  have hR1 : 1 < R := by linarith
  have hcoeff : Summable (fun n : ℕ => |zetaHorizontalPrimeCoeff R n|) := by
    refine (summable_weight 2 hR1).congr fun n => ?_
    change weight 2 R n = |weight 2 R n|
    exact (abs_of_nonneg (weight_nonneg 2 R n)).symm
  have hphase : Summable (fun n : ℕ =>
      |zetaHorizontalPrimeCoeff R n * Real.cos (t * Real.log (n : ℝ))|) := by
    simpa only [primeTerm, weight, zetaHorizontalPrimeCoeff, Real.norm_eq_abs] using
      summable_norm_primeTerm 2 hR1 t
  refine ⟨hcoeff, hphase, ?_⟩
  change (∫ σ : ℝ in Ioi R, Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) = _
  calc
    (∫ σ : ℝ in Ioi R, Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) =
        ∫ σ : ℝ in Ioi R, ∑' n : ℕ, primeTerm 1 σ t n := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro σ hσ
      exact log_norm_eq_prime_tsum (hR.trans hσ.le) t
    _ = ∑' n : ℕ, ∫ σ : ℝ in Ioi R, primeTerm 1 σ t n :=
      (integral_tsum_of_summable_integral_norm
        (integrableOn_primeTerm 1 R t) (summable_integral_norm_primeTerm 1 hR1 t)).symm
    _ = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ R * (Real.log (n : ℝ)) ^ 2)) *
          Real.cos (t * Real.log (n : ℝ)) := by
      exact tsum_congr (integral_primeTerm 1 R t)

end Zeta23.RvM
