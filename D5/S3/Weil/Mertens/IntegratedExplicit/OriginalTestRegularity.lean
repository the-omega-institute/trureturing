/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual prefix correlation and finite-measure spectral resolvents are absolutely continuous. -/

import D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
The original correlation integral uses AtomicPrefixEnergy and its finite
interval-intersection identity. The spectralS function is the cosine resolvent
of its input measure, with no evenness assumption.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace OriginalTestRegularity

open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy

def ramp (a t : ℝ) : ℝ := max (a - t) 0

lemma ramp_lipschitz (a : ℝ) : LipschitzWith 1 (ramp a) := by
  have hlin : LipschitzWith 1 (fun t : ℝ => a - t) := by
    apply LipschitzWith.mk_one
    intro x y
    simp only [Real.dist_eq]
    have he : (a - x) - (a - y) = -(x - y) := by ring
    rw [he, abs_neg]
  exact hlin.max_const 0

lemma finite_sum_ac {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} {a b : ℝ}
    (hF : ∀ i ∈ s, AbsolutelyContinuousOnInterval (F i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, F i t) a b := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
  | @insert i s hi ih =>
    intro hF
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- The original correlation integral, without a finite-formula definition. -/
def c {ι : Type*} [Fintype ι] (x : ι → ℝ) (a : ι → ℂ) (t : ℝ) : ℝ :=
  (∫ u : ℝ, star («prefix» x a (u + t)) * «prefix» x a u).re

lemma c_eq_hinges {ι : Type*} [Fintype ι] (x : ι → ℝ) (a : ι → ℂ)
    (ha : ∑ i, a i = 0) (t : ℝ) :
    c x a t = -(∑ i, ∑ j, (star (a i) * a j).re * ramp (x i - x j) t) := by
  have hh := (shifted_hinge_prefix_energy x a ha t).2.2.1
  have he : (∫ u : ℝ, star («prefix» x a (u + t)) * «prefix» x a u) =
      -(∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - t) 0 : ℝ) : ℂ)) := by
    simpa only [neg_neg] using congrArg Neg.neg hh.symm
  unfold c
  rw [he]
  simp only [Complex.neg_re, Complex.re_sum, Complex.re_mul_ofReal, ramp]

/-- Piecewise affine c is AC, including repeated nodes and the empty type. -/
theorem c_ac {ι : Type*} [Fintype ι] (x : ι → ℝ) (a : ι → ℂ)
    (ha : ∑ i, a i = 0) (l r : ℝ) : AbsolutelyContinuousOnInterval (c x a) l r := by
  have he : c x a = fun t =>
      -(∑ i, ∑ j, (star (a i) * a j).re * ramp (x i - x j) t) := by
    funext t
    exact c_eq_hinges x a ha t
  rw [he]
  apply AbsolutelyContinuousOnInterval.neg
  apply finite_sum_ac Finset.univ
  intro i _
  apply finite_sum_ac Finset.univ
  intro j _
  exact ((ramp_lipschitz (x i - x j)).lipschitzOnWith.absolutelyContinuousOnInterval).const_mul
    (star (a i) * a j).re

theorem c_at_D {ι : Type*} [Fintype ι] (x : ι → ℝ) (a : ι → ℂ)
    (ha : ∑ i, a i = 0) {D : ℝ} (hx : ∀ i, x i ∈ Icc 0 D) : c x a D = 0 := by
  classical
  rw [c_eq_hinges x a ha D]
  have he (i j : ι) : ramp (x i - x j) D = 0 := by
    exact max_eq_right (by linarith [(hx i).2, (hx j).1])
  simp only [he, mul_zero, Finset.sum_const_zero, neg_zero]

def spectralKernel (t w : ℝ) : ℝ := Real.cos (w * t) / (1 + 4 * w ^ 2)

def spectralS (ρ : Measure ℝ) (t : ℝ) : ℝ := ∫ w, spectralKernel t w ∂ρ

lemma denom_pos (w : ℝ) : 0 < 1 + 4 * w ^ 2 := by positivity

lemma spectralKernel_continuous (t : ℝ) : Continuous (spectralKernel t) := by
  unfold spectralKernel
  exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).div
    (continuous_const.add (continuous_const.mul (continuous_id.pow 2)))
    (fun w => (denom_pos w).ne')

lemma spectralKernel_bound (t w : ℝ) : |spectralKernel t w| ≤ 1 := by
  rw [spectralKernel, abs_div, abs_of_pos (denom_pos w)]
  apply (div_le_one (denom_pos w)).mpr
  exact (Real.abs_cos_le_one _).trans (by nlinarith [sq_nonneg w])

lemma spectralKernel_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    Integrable (spectralKernel t) ρ := by
  apply (integrable_const (1 : ℝ)).mono' (spectralKernel_continuous t).aestronglyMeasurable
  exact Eventually.of_forall (fun w => by simpa [Real.norm_eq_abs] using spectralKernel_bound t w)

theorem spectralS_ac (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a b : ℝ) :
    AbsolutelyContinuousOnInterval (spectralS ρ) a b := by
  have hLip : LipschitzWith (Real.toNNReal (ρ.real univ / 4)) (spectralS ρ) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    have hpoint (w : ℝ) : |spectralKernel x w - spectralKernel y w| ≤ |x - y| / 4 := by
      have hnum := Real.abs_cos_sub_cos_le (w * x) (w * y)
      have hweight : |w| / (1 + 4 * w ^ 2) ≤ 1 / 4 := by
        apply (div_le_iff₀ (denom_pos w)).mpr
        nlinarith [sq_nonneg (2 * |w| - 1), sq_abs w]
      calc
        _ = |Real.cos (w * x) - Real.cos (w * y)| / (1 + 4 * w ^ 2) := by
          simp only [spectralKernel, ← sub_div, abs_div, abs_of_pos (denom_pos w)]
        _ ≤ |w * x - w * y| / (1 + 4 * w ^ 2) :=
          div_le_div_of_nonneg_right hnum (denom_pos w).le
        _ = (|w| / (1 + 4 * w ^ 2)) * |x - y| := by
          rw [← mul_sub, abs_mul]; ring
        _ ≤ (1 / 4) * |x - y| := mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
        _ = _ := by ring
    have hb := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun w => spectralKernel x w - spectralKernel y w)
      (Eventually.of_forall (fun w => by simpa [Real.norm_eq_abs] using hpoint w))
    rw [integral_sub (spectralKernel_integrable ρ x) (spectralKernel_integrable ρ y)] at hb
    change ‖spectralS ρ x - spectralS ρ y‖ ≤ _ at hb
    simpa [Real.dist_eq, Real.norm_eq_abs, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using hb
  exact hLip.lipschitzOnWith.absolutelyContinuousOnInterval

end OriginalTestRegularity
