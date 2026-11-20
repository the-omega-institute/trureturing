/- GID: D5/S3/Analytic/Laplace/MaximalRealPartProjection
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/MaximalRealPartProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolutely summable exponential series project asymptotically onto a bounding real-part line. -/

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Maximal real-part projection of an exponential series

For an absolutely summable coefficient sequence, the terms on the real-part
line `Θ` give a uniformly continuous Fourier series. Each lower term decays
after normalization at `Θ`, with the coefficient norms as a common majorant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology Uniformity

namespace MaximalRealPartProjection

private def normalizedTerm (a z : ℕ → ℂ) (Θ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  a n * Complex.exp ((t : ℂ) * (z n - (Θ : ℂ)))

private def normalizedSeries (a z : ℕ → ℂ) (Θ t : ℝ) : ℂ :=
  ∑' n, normalizedTerm a z Θ n t

private def maximalTerm (a z : ℕ → ℂ) (Θ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  if (z n).re = Θ then normalizedTerm a z Θ n t else 0

def maximalSeries (a z : ℕ → ℂ) (Θ t : ℝ) : ℂ :=
  ∑' n, maximalTerm a z Θ n t

variable {a z : ℕ → ℂ} {Θ : ℝ}

private theorem shiftedExponent_re (w : ℂ) (Θ t : ℝ) :
    ((t : ℂ) * (w - (Θ : ℂ))).re = t * (w.re - Θ) := by
  rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]

private theorem norm_normalizedTerm (n : ℕ) (t : ℝ) :
    ‖normalizedTerm a z Θ n t‖ = ‖a n‖ * Real.exp (t * ((z n).re - Θ)) := by
  rw [normalizedTerm, norm_mul, Complex.norm_exp, shiftedExponent_re]

private theorem norm_normalizedTerm_le (hz : ∀ n, (z n).re ≤ Θ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖normalizedTerm a z Θ n t‖ ≤ ‖a n‖ := by
  rw [norm_normalizedTerm]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr (hz n))))

private theorem norm_maximalTerm_le (n : ℕ) (t : ℝ) :
    ‖maximalTerm a z Θ n t‖ ≤ ‖a n‖ := by
  by_cases hn : (z n).re = Θ
  · rw [maximalTerm, ite_eq_left hn, norm_normalizedTerm, hn, sub_self, mul_zero,
      Real.exp_zero, mul_one]
  · simp only [maximalTerm, ite_eq_right hn, norm_zero, norm_nonneg]

private theorem summable_norm_maximalTerm (ha : Summable (fun n => ‖a n‖)) (t : ℝ) :
    Summable (fun n => ‖maximalTerm a z Θ n t‖) :=
  ha.of_norm_bounded (fun n => by
    simpa only [norm_norm] using (norm_maximalTerm_le (a := a) (z := z) (Θ := Θ) n t))

private theorem maximalSeries_hasSumUniformlyOn (ha : Summable (fun n => ‖a n‖)) :
    HasSumUniformlyOn (maximalTerm a z Θ) (maximalSeries a z Θ) (Set.univ : Set ℝ) :=
  HasSumUniformlyOn.of_norm_le_summable (f := maximalTerm a z Θ) ha
    (fun n t _ => norm_maximalTerm_le n t)

private theorem uniformContinuous_maximalTerm (n : ℕ) :
    UniformContinuous (maximalTerm a z Θ n) := by
  by_cases hn : (z n).re = Θ
  · have harg : UniformContinuous (fun t : ℝ => (t : ℂ) * (z n - (Θ : ℂ))) :=
      Complex.isometry_ofReal.uniformContinuous.mul_const' _
    have hphase :
        UniformContinuous (fun t : ℝ => Complex.exp ((t : ℂ) * (z n - (Θ : ℂ)))) := by
      apply uniformContinuousOn_univ.mp
      refine (UniformContinuousOn.cexp 0).comp harg.uniformContinuousOn ?_
      intro t _
      change ((t : ℂ) * (z n - (Θ : ℂ))).re ≤ 0
      simp [shiftedExponent_re, hn]
    have heq : maximalTerm a z Θ n =
        (fun t : ℝ => a n * Complex.exp ((t : ℂ) * (z n - (Θ : ℂ)))) := by
      funext t
      simp [maximalTerm, hn, normalizedTerm]
    rw [heq]
    exact hphase.const_mul' (a n)
  · have heq : maximalTerm a z Θ n = fun _ : ℝ => (0 : ℂ) := by
      funext t
      simp [maximalTerm, hn]
    rw [heq]
    exact uniformContinuous_const

theorem uniformContinuous_maximalSeries (ha : Summable (fun n => ‖a n‖)) :
    UniformContinuous (maximalSeries a z Θ) := by
  apply (tendstoUniformlyOn_univ.mp
    (maximalSeries_hasSumUniformlyOn (z := z) (Θ := Θ) ha).tendstoUniformlyOn).uniformContinuous
  apply Frequently.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact uniformContinuous_const
  | @insert n s hn ih =>
    simpa only [Finset.sum_insert hn] using
      (uniformContinuous_maximalTerm (a := a) (z := z) (Θ := Θ) n).add ih

/-- The strict lower terms are dominated by the coefficient norms for `t ≥ 0`. -/
private theorem tendsto_normalizedSeries_sub_maximalSeries
    (ha : Summable (fun n => ‖a n‖)) (hz : ∀ n, (z n).re ≤ Θ) :
    Tendsto (fun t => normalizedSeries a z Θ t - maximalSeries a z Θ t) atTop (𝓝 (0 : ℂ)) := by
  let r : ℝ → ℕ → ℂ := fun t n => normalizedTerm a z Θ n t - maximalTerm a z Θ n t
  have hterm (n : ℕ) : Tendsto (fun t => r t n) atTop (𝓝 (0 : ℂ)) := by
    by_cases hn : (z n).re = Θ
    · simpa only [r, maximalTerm, ite_eq_left hn, sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    · have hneg : (z n).re - Θ < 0 := sub_neg.mpr (lt_of_le_of_ne (hz n) hn)
      have harg : Tendsto (fun t : ℝ => t * ((z n).re - Θ)) atTop atBot :=
        (tendsto_mul_const_atBot_of_neg hneg).mpr tendsto_id
      simp only [r, maximalTerm, ite_eq_right hn, sub_zero]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [norm_normalizedTerm, Function.comp_def, mul_zero] using
        (Real.tendsto_exp_atBot.comp harg).const_mul ‖a n‖
  have hbound : ∀ᶠ t in atTop, ∀ n, ‖r t n‖ ≤ ‖a n‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht n
    by_cases hn : (z n).re = Θ
    · simp only [r, maximalTerm, ite_eq_left hn, sub_self, norm_zero, norm_nonneg]
    · simpa only [r, maximalTerm, ite_eq_right hn, sub_zero] using
        norm_normalizedTerm_le (a := a) hz n ht
  have htail : Tendsto (fun t => ∑' n, r t n) atTop (𝓝 (0 : ℂ)) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence ha hterm hbound
  apply htail.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hf : Summable (fun n => normalizedTerm a z Θ n t) :=
    ha.of_norm_bounded (fun n => norm_normalizedTerm_le hz n ht)
  have hH : Summable (fun n => maximalTerm a z Θ n t) :=
    (summable_norm_maximalTerm ha t).of_norm
  exact hf.tsum_sub hH

private theorem normalizedSeries_eq_exp_mul_tsum (a z : ℕ → ℂ) (Θ t : ℝ) :
    normalizedSeries a z Θ t =
      (Real.exp (-Θ * t) : ℂ) * (∑' n, a n * Complex.exp ((t : ℂ) * z n)) := by
  unfold normalizedSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have harg : (t : ℂ) * (z n - (Θ : ℂ)) =
      ((-Θ * t : ℝ) : ℂ) + (t : ℂ) * z n := by
    rw [Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [normalizedTerm, harg, Complex.ofReal_exp, Complex.exp_add]
  ac_rfl

theorem tendsto_exp_mul_tsum_sub_maximalSeries
    (ha : Summable (fun n => ‖a n‖)) (hz : ∀ n, (z n).re ≤ Θ) :
    Tendsto (fun t : ℝ =>
      (Real.exp (-Θ * t) : ℂ) * (∑' n, a n * Complex.exp ((t : ℂ) * z n)) -
        maximalSeries a z Θ t) atTop (𝓝 (0 : ℂ)) := by
  simpa only [normalizedSeries_eq_exp_mul_tsum] using
    tendsto_normalizedSeries_sub_maximalSeries ha hz

end MaximalRealPartProjection
