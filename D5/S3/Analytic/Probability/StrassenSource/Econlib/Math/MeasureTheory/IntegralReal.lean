/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Real Bochner / lintegral helper lemmas

Measure-theoretic facts about real-valued Bochner integrals: Building integrability and unit total
mass from a unit `ofReal`-lintegral, strict positivity of an integral from positivity on a
positive-measure set, and additivity of a set integral over two adjacent closed intervals.

## Main results

* `MeasureTheory.integrable_of_lintegral_ofReal_eq_one` — a nonnegative strongly measurable density
  with unit `ofReal`-lintegral is `Integrable`.
* `MeasureTheory.integral_eq_one_of_lintegral_ofReal_eq_one` — the same hypotheses force
  `∫ density = 1`.
* `MeasureTheory.integral_pos_of_pos_on` — an a.e.-nonnegative integrable function that is strictly
  positive on a positive-measure set has strictly positive integral.
* `MeasureTheory.integral_Icc_split` — adjacent-interval additivity of the set integral over closed
  intervals.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace MeasureTheory

/-- A nonnegative strongly measurable density with unit `ofReal`-lintegral is integrable. -/
lemma integrable_of_lintegral_ofReal_eq_one {density : ℝ → ℝ}
    (nonneg : ∀ x, 0 ≤ density x) (h_meas : StronglyMeasurable density)
    (h_lintegral : ∫⁻ x, ENNReal.ofReal (density x) = 1) :
    Integrable density volume :=
  (lintegral_ofReal_ne_top_iff_integrable h_meas.aestronglyMeasurable
    (ae_of_all _ nonneg)).mp (by rw [h_lintegral]; exact ENNReal.one_ne_top)

/-- A nonnegative density with unit `ofReal`-lintegral has total mass `1`. -/
lemma integral_eq_one_of_lintegral_ofReal_eq_one {density : ℝ → ℝ}
    (nonneg : ∀ x, 0 ≤ density x) (h_meas : StronglyMeasurable density)
    (h_lintegral : ∫⁻ x, ENNReal.ofReal (density x) = 1) :
    ∫ x, density x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ nonneg) h_meas.aestronglyMeasurable,
    h_lintegral]
  simp

/-- An a.e.-nonnegative integrable function that is strictly positive on a set of positive measure
has strictly positive integral. -/
lemma integral_pos_of_pos_on {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hle' : 0 ≤ᵐ[μ] g) (hint : Integrable g μ)
    {s : Set α} (hμs : 0 < μ s) (hgs : ∀ x ∈ s, 0 < g x) :
    0 < ∫ x, g x ∂μ := by
  have hsupp : 0 < μ (Function.support g) :=
    lt_of_lt_of_le hμs (measure_mono fun x hx => ne_of_gt (hgs x hx))
  exact (integral_pos_iff_support_of_nonneg_ae hle' hint).mpr hsupp

/-- Adjacent-interval split for any integrable function on `[p, r]` with `p ≤ q ≤ r`. -/
lemma integral_Icc_split {f : ℝ → ℝ} {p q r : ℝ} (hpq : p ≤ q) (hqr : q ≤ r)
    (hf : IntegrableOn f (Icc p r)) :
    ∫ x in Icc p r, f x = (∫ x in Icc p q, f x) + ∫ x in Icc q r, f x := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpq, ← intervalIntegral.integral_of_le hqr,
    ← intervalIntegral.integral_of_le (hpq.trans hqr)]
  refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
    exact hf.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hqr)) le_rfl
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hqr]
    exact hf.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc hpq le_rfl)) le_rfl

end MeasureTheory
