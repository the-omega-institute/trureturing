/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.Analysis.HingeConvex
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.Probability.QuantileStopLoss
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Convex.Basic

/-!
# Stop-loss and the convex order

The **stop-loss order** compares laws by their stop-loss transforms `z ↦ E[(x - z)⁺]`. This file
derives, from the convex order on a compact interval, that convex dominance forces pointwise
domination of stop-loss functions, and turns that into a Markov-type tail bound and the
integrated-quantile inequalities (upper increasing, lower decreasing under the equal-mean
condition).

## Main statements

* `stopLoss_le_of_convexOrderOnIcc` — convex order forces pointwise stop-loss domination.
* `mul_measureReal_Ici_le_stopLoss_of_convexOrderOnIcc` — a Markov-type tail bound for the lower
  law in terms of the upper law's stop-loss transform.
* `upperIntegratedQuantile_le_of_convexOrderOnIcc`,
  `lowerIntegratedQuantile_ge_of_convexOrderOnIcc` — the upper and lower integrated-quantile
  inequalities under convex order.

## Notes

The forward implication `μ ≼cx[a,b] ν ⟹ stopLoss μ ≤ stopLoss ν` is a direct instance of
`ConvexOrderOnIcc` applied to the convex hinge `x ↦ (x - z)⁺`.

## Tags

stop-loss order, convex order, integrated quantile, tail bound
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Econlib.Probability

/-- The hinge/stop-loss test function `x ↦ max (x - z) 0` is convex on any set. -/
lemma convexOn_hinge_on (a b z : ℝ) :
    ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => max (x - z) 0) := by
  have h_univ : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => max (x - z) 0) :=
    convexOn_hinge_right z
  exact h_univ.subset (subset_univ _) (convex_Icc a b)

/-- The hinge test function is continuous. -/
lemma continuous_hinge (z : ℝ) : Continuous (fun x : ℝ => max (x - z) 0) :=
  (continuous_id.sub continuous_const).max continuous_const

/-- **Stop-loss monotonicity under convex order.** If `μ ≼cx[a,b] ν`, then the stop-loss function
of `μ` is pointwise bounded by the stop-loss function of `ν`. -/
lemma stopLoss_le_of_convexOrderOnIcc {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) (z : ℝ) :
    μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z := by
  -- `stopLoss d z = d.expect (fun x => max (x - z) 0)`; apply `h.convex_expect_le`.
  have hconv : ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => max (x - z) 0) :=
    convexOn_hinge_on a b z
  have hcont : ContinuousOn (fun x : ℝ => max (x - z) 0) (Set.Icc a b) :=
    (continuous_hinge z).continuousOn
  have hexpect := h.convex_expect_le _ hconv hcont
  exact hexpect

/-- **Tail bound under convex order.** If `μ ≼cx[a,b] ν`, then `(r - s) · μ[r, ∞) ≤ stopLoss ν s`
for every hinge point `s` and threshold `r`. Optimizing over `s` gives a tight tail bound on the
lower law in terms of the upper law's stop-loss transform. -/
lemma mul_measureReal_Ici_le_stopLoss_of_convexOrderOnIcc {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) (s r : ℝ) :
    (r - s) * μ.toMeasure.real (Ici r) ≤ ν.toMeasure.stopLoss s := by
  have hμ_int : Integrable (fun x : ℝ => x) μ.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_left
  exact le_trans (Measure.mul_measureReal_Ici_le_stopLoss hμ_int s r)
    (stopLoss_le_of_convexOrderOnIcc h s)

/-! ### Integrated-quantile inequalities under the convex order -/

/-- **Upper integrated-quantile inequality under convex order.** For compact-supported
`μ ≼cx[a,b] ν` and `t ∈ (0, 1]`, the upper integrated quantile of `μ` is at most that of `ν`. -/
theorem upperIntegratedQuantile_le_of_convexOrderOnIcc {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) ≤
    (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u) := by
  obtain ⟨ht0, ht1⟩ := ht
  -- Handle t = 1 degenerately.
  rcases eq_or_lt_of_le ht1 with ht1_eq | ht1_lt
  · subst ht1_eq
    rw [Set.Ioc_self, setIntegral_empty, setIntegral_empty]
  -- Main case: 0 < t < 1.
  set z := MeasureTheory.Measure.quantile ν.toMeasure t with hz_def
  -- Integrability of `id` for μ and ν from compact support on `[a, b]`.
  have hμ_int : Integrable (fun x : ℝ => x) μ.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_left
  have hν_int : Integrable (fun x : ℝ => x) ν.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_right
  have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
  have ht_Ioo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht1_lt⟩
  -- Step 1: universal bound for μ at z.
  have h_step1 : (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) ≤
      μ.toMeasure.stopLoss z + z * (1 - t) :=
    MeasureTheory.Measure.upperIntegratedQuantile_le_stopLoss_add hμ_int ht_Icc z
  -- Step 2: stop-loss monotonicity.
  have h_step2 : μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z :=
    stopLoss_le_of_convexOrderOnIcc h z
  -- Step 3: equality for ν at z = quantile ν.toMeasure t.
  have h_step3 : ν.toMeasure.stopLoss z + z * (1 - t) =
      ∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u :=
    (MeasureTheory.Measure.upperIntegratedQuantile_eq_stopLoss_add hν_int ht_Ioo).symm
  -- Chain.
  linarith

/-- **Lower integrated-quantile inequality under convex order.** For compact-supported
`μ ≼cx[a,b] ν` and `t ∈ (0, 1]`, the lower integrated quantile of `ν` is at most that of `μ`. -/
theorem lowerIntegratedQuantile_ge_of_convexOrderOnIcc {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (∫ u in Set.Ioc 0 t, MeasureTheory.Measure.quantile ν.toMeasure u) ≤
    (∫ u in Set.Ioc 0 t, MeasureTheory.Measure.quantile μ.toMeasure u) := by
  obtain ⟨ht0, ht1⟩ := ht
  -- Integrability of `id` for μ and ν from compact support on `[a, b]`.
  have hμ_int : Integrable (fun x : ℝ => x) μ.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_left
  have hν_int : Integrable (fun x : ℝ => x) ν.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_right
  -- Step: ∫ Ioo 0 1, q_μ = μ.expect id (via pushforward), similarly for ν. Then mean_eq gives
  -- ∫ Ioo 0 1, q_μ = ∫ Ioo 0 1, q_ν.
  -- Split each into Ioc 0 t + Ioc t 1 and use upper inequality on Ioc t 1.
  have h_mean_eq : μ.expect id = ν.expect id := h.mean_eq
  -- Use integral_eq_integral_quantile to compute expect id as ∫ Ioo 0 1, q.
  -- `expect id` equals the integrated quantile over `Ioo 0 1` (pushforward to the unit interval).
  have h_pushforward : ∀ d : ProbDist ℝ, d.expect id =
      ∫ u in Set.Ioo (0 : ℝ) 1, MeasureTheory.Measure.quantile d.toMeasure u := fun d => by
    unfold ProbDist.expect
    exact MeasureTheory.Measure.integral_eq_integral_quantile (fun x => x)
      aestronglyMeasurable_id
  have h_μ_pushforward := h_pushforward μ
  have h_ν_pushforward := h_pushforward ν
  -- Split the integral: ∫ Ioo 0 1 = ∫ Ioc 0 t + ∫ Ioc t 1.
  have h_split_μ : (∫ u in Set.Ioo (0 : ℝ) 1,
        MeasureTheory.Measure.quantile μ.toMeasure u) =
      (∫ u in Set.Ioc (0 : ℝ) t, MeasureTheory.Measure.quantile μ.toMeasure u) +
      (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) :=
    MeasureTheory.Measure.integral_quantile_Ioo_split hμ_int ht0 ht1
  have h_split_ν : (∫ u in Set.Ioo (0 : ℝ) 1,
        MeasureTheory.Measure.quantile ν.toMeasure u) =
      (∫ u in Set.Ioc (0 : ℝ) t, MeasureTheory.Measure.quantile ν.toMeasure u) +
      (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u) :=
    MeasureTheory.Measure.integral_quantile_Ioo_split hν_int ht0 ht1
  -- ∫ Ioo q_μ = ∫ Ioo q_ν.
  have h_total : (∫ u in Set.Ioo (0 : ℝ) 1,
        MeasureTheory.Measure.quantile μ.toMeasure u) =
      (∫ u in Set.Ioo (0 : ℝ) 1, MeasureTheory.Measure.quantile ν.toMeasure u) := by
    rw [← h_μ_pushforward, ← h_ν_pushforward, h_mean_eq]
  -- Upper inequality on Ioc t 1.
  have h_upper : (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) ≤
      (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u) :=
    upperIntegratedQuantile_le_of_convexOrderOnIcc h ⟨ht0, ht1⟩
  -- Combine: ∫ Ioc 0 t, q_μ = (∫ Ioo q_μ) - ∫ Ioc t 1, q_μ
  --                       = (∫ Ioo q_ν) - ∫ Ioc t 1, q_μ
  --                       ≥ (∫ Ioo q_ν) - ∫ Ioc t 1, q_ν
  --                       = ∫ Ioc 0 t, q_ν.
  linarith

end Econlib.Probability

end
