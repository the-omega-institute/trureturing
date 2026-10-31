/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local positive representation of the complete arithmetic prime kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import D5.S3.Analytic.ExpRatioCM.Series
import D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Analytic.ExpRatioCM.Series

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

/-- The full arithmetic kernel, retaining every Mangoldt ramp and trivial zero. -/
def K (t : ℝ) : ℝ :=
  Real.exp (-|t| / 2) * (U (Real.exp |t|) - Real.log (2 * Real.pi) + trivialT |t|)

private def b : ℕ → ℝ
  | 0 => 0
  | n + 1 => trivialCoeff n

private lemma b_bound (n : ℕ) : |b n| ≤ (1 : ℝ) ^ n := by
  cases n with
  | zero => simp [b]
  | succ n =>
    rw [b, abs_of_nonneg (trivialCoeff_nonneg n), one_pow]
    unfold trivialCoeff
    apply (div_le_one (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

private lemma trivialT_eq_weighted {t : ℝ} (ht : 0 < t) : trivialT t = weightedSeries b 0 (2 * t) := by
  symm
  unfold weightedSeries
  rw [((summable_weighted zero_lt_one b_bound 0 (by simpa using (show 0 < 2 * t by linarith))).of_norm).tsum_eq_zero_add]
  simp only [b, Nat.cast_zero, pow_zero, mul_one, zero_mul, neg_zero, Real.exp_zero,
    zero_add, Nat.cast_add, Nat.cast_one]
  congr 1
  funext n
  congr 2
  ring

private lemma mangoldtPart_exp_eq_zero {t : ℝ} (ht : t < Real.log 2) :
    mangoldtPart (Real.exp t) = 0 := by
  apply tsum_eq_zero
  intro n
  rcases n with _ | _ | n
  · simp [mangoldtRamp]
  · simp [mangoldtRamp]
  · have hn : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have he : Real.exp t < (n + 2 : ℕ) :=
      (Real.exp_lt_exp.mpr ht).trans_le (by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n])
    rw [mangoldtRamp, max_eq_right (by
      have := (div_lt_one hn).mpr he
      linarith), mul_zero]

private lemma K_eq_local {t : ℝ} (ht : 0 ≤ t) (ht2 : t < Real.log 2) :
    K t = Real.exp (-t / 2) *
      (Real.exp t * (1 + Real.eulerMascheroniConstant - t) -
        Real.log (2 * Real.pi) + trivialT t) := by
  rw [K, abs_of_nonneg ht, U_eq_complete_ramps (Real.exp_nonneg t),
    mangoldtPart_exp_eq_zero ht2, Real.log_exp]
  ring

private lemma K_zero : K 0 = firstLiMass := by
  rw [K_eq_local le_rfl (Real.log_pos (by norm_num)), firstLiMass_split]
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, sub_zero, one_mul]
  have hT : trivialT 0 = 1 - Real.log 2 := by
    simpa [trivialT] using trivialCoeff_hasSum.tsum_eq
  rw [hT, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

private lemma K_zero_pos : 0 < K 0 := by
  rw [K_zero, firstLiMass]
  linarith [D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity.first_li_coefficient_pos]

private lemma log_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-(n : ℝ) * (2 * t)) / (n : ℝ))
      (-Real.log (1 - Real.exp (-(2 * t)))) := by
  have he : Real.exp (-(2 * t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log
    (z := (Real.exp (-(2 * t)) : ℂ)) (by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] using he))
  convert hs using 1
  · funext n
    rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div, Complex.ofReal_re, ← Real.exp_nat_mul]
    congr 2
    ring
  · rw [show (1 : ℂ) - (Real.exp (-(2 * t)) : ℂ) =
        ((1 - Real.exp (-(2 * t)) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (by linarith : 0 ≤ 1 - Real.exp (-(2 * t)))]
    simp

private lemma trivialT_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt trivialT (trivialT t + Real.log (1 - Real.exp (-(2 * t))) / 2) t := by
  have hw (k : ℕ) := (summable_weighted zero_lt_one b_bound k
    (by simpa using (show 0 < 2 * t by linarith))).of_norm
  have hs := (hw 0).add ((hw 1).mul_left 2)
  have heq : weightedSeries b 0 (2 * t) + 2 * weightedSeries b 1 (2 * t) =
      -Real.log (1 - Real.exp (-(2 * t))) / 2 := by
    apply HasSum.unique hs.hasSum ?_
    convert (log_series ht).div_const 2 using 1
    funext n
    cases n with
    | zero => simp [b]
    | succ n =>
      simp only [b, pow_zero, mul_one, pow_one, Nat.cast_add, Nat.cast_one]
      unfold trivialCoeff
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn' : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
      field_simp [hn, hn']
      <;> ring
  have hd := (hasDerivAt_weighted zero_lt_one b_bound 0
    (by simpa using (show 0 < 2 * t by linarith))).comp t
      ((hasDerivAt_id t).const_mul 2)
  have hloc : trivialT =ᶠ[𝓝 t] (fun u => weightedSeries b 0 (2 * u)) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu using trivialT_eq_weighted hu
  convert hd.congr_of_eventuallyEq hloc using 1
  rw [trivialT_eq_weighted ht]
  change _ = -weightedSeries b 1 (2 * t) * 2
  linarith

private def D1 (t : ℝ) : ℝ := K t / 2 - Real.exp (t / 2) +
  Real.exp (-t / 2) * (Real.log (2 * Real.pi) + Real.log (1 - Real.exp (-(2 * t))) / 2)

private def D2 (t : ℝ) : ℝ := K t / 4 - Real.exp (t / 2) +
  Real.exp (-t / 2) / (Real.exp (2 * t) - 1)

private lemma hasDerivAt_K {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt K (D1 t) t := by
  have hd := (((hasDerivAt_id t).neg.div_const 2).exp).mul
    ((((Real.hasDerivAt_exp t).mul
      ((hasDerivAt_const t (1 + Real.eulerMascheroniConstant)).sub (hasDerivAt_id t))).sub_const
        (Real.log (2 * Real.pi))).add (trivialT_derivative ht))
  have hloc : K =ᶠ[𝓝 t] (fun u => Real.exp (-u / 2) *
      (Real.exp u * (1 + Real.eulerMascheroniConstant - u) -
        Real.log (2 * Real.pi) + trivialT u)) := by
    filter_upwards [Ioo_mem_nhds ht ht2] with u hu using K_eq_local hu.1.le hu.2
  convert hd.congr_of_eventuallyEq hloc using 1
  rw [D1, K_eq_local ht.le ht2]
  have he : Real.exp (t / 2) = Real.exp (-t / 2) * Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  ring

private lemma log_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))))
      (2 / (Real.exp (2 * t) - 1)) t := by
  have hpos : 0 < 2 * t := by linarith
  have hd :=
    (D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives.log_one_sub_exp_derivatives.1.
      differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).differentiableAt
        (Ioi_mem_nhds hpos)
  have hh := hd.hasDerivAt
  rw [(D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives.log_one_sub_exp_derivatives.2
    (2 * t) hpos).1] at hh
  convert hh.comp t ((hasDerivAt_id t).const_mul 2) using 1 <;> ring

private lemma hasDerivAt_D1 {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt D1 (D2 t) t := by
  have hd := (((hasDerivAt_K ht ht2).div_const 2).sub
    (((hasDerivAt_id t).div_const 2).exp)).add
      ((((hasDerivAt_id t).neg.div_const 2).exp).mul
        ((hasDerivAt_const t (Real.log (2 * Real.pi))).add
          ((log_hasDerivAt ht).div_const 2)))
  convert hd using 1
  · rfl
  · dsimp only [D1, D2]
    ring

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

