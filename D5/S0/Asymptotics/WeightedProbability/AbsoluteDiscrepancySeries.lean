/- GID: D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Quadratic tails force reciprocal square-root logarithmic series divergence. -/

import D5.S0.Asymptotics.WeightedProbability.UniformLowerQuantileSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
The estimates and series implication are unbounded symbolic statements, rather
than finite computations or certified instances.

The private inverse-log lemma is adapted from
`RemyDegenne/Wang2026Almost`, revision
`5cd4a65235928aadc7a02fe5a051eeb056eed239`, file
`Wang2026Almost/Mathlib/Analysis/SpecialFunctions/Log/Summable.lean`.
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
The full Apache 2.0 license is retained at the repository root.
This adaptation changes module/namespace visibility and qualifies logarithms.
Retire the private port when the repository's own pinned mathlib exports an
exact directly applicable proof of `¬ Summable (fun n : ℕ =>
((n : ℝ) * Real.log n)⁻¹)`, verified by a guarded exact application with only
`propext`, `Classical.choice` and `Quot.sound` in its axiom closure; switch its
live consumer to that declaration.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries

noncomputable def discrepancyProfile (x : ℤ) : ℝ :=
  1 / (Real.sqrt (2 + |(x : ℝ)|) * Real.log (2 + |(x : ℝ)|))

noncomputable def shiftedLogWeight (j : ℕ) : ℝ :=
  1 / (((j : ℝ) + 1) * Real.log ((j : ℝ) + 2))

private lemma not_summable_inv_mul_log :
    ¬ Summable (fun n : ℕ ↦ ((n : ℝ) * Real.log n)⁻¹) := by
  rw [← summable_condensed_iff_of_eventually_nonneg]
  · have h : (fun k : ℕ ↦ (2 : ℝ) ^ k * ((2 ^ k : ℕ) * Real.log (2 ^ k : ℕ) : ℝ)⁻¹)
        = fun k : ℕ ↦ (Real.log 2)⁻¹ * (k : ℝ)⁻¹ := by
      ext k
      push_cast
      rw [Real.log_pow, mul_inv, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (by positivity), one_mul, mul_comm]
    rw [h, summable_mul_left_iff (inv_ne_zero (Real.log_pos one_lt_two).ne')]
    exact Real.not_summable_natCast_inv
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.log_nonneg this
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    have hlog' : 0 < Real.log (n + 1) := Real.log_pos (by linarith)
    push_cast
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact mul_le_mul (by linarith)
      (Real.log_le_log (by linarith) (by linarith)) hlog.le (by linarith)

private lemma shiftedLogWeight_pos (j : ℕ) : 0 < shiftedLogWeight j := by
  unfold shiftedLogWeight
  apply one_div_pos.mpr
  exact mul_pos (by positivity)
    (Real.log_pos (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]))

/-- The exact source weights diverge in the extended nonnegative reals. -/
theorem tsum_shiftedLogWeight_eq_top :
    ∑' j, ENNReal.ofReal (shiftedLogWeight j) = ∞ := by
  by_contra hfinite
  have hsum : Summable shiftedLogWeight := by
    simpa only [ENNReal.toReal_ofReal (shiftedLogWeight_pos _).le] using
      ENNReal.summable_toReal hfinite
  apply not_summable_inv_mul_log
  apply (summable_nat_add_iff 2).mp
  apply Summable.of_nonneg_of_le (fun j => by positivity) ?_ hsum
  intro j
  change (((j + 2 : ℕ) : ℝ) * Real.log (j + 2 : ℕ))⁻¹ ≤
    1 / (((j : ℝ) + 1) * Real.log ((j : ℝ) + 2))
  push_cast
  have hlog : 0 < Real.log ((j : ℝ) + 2) :=
    Real.log_pos (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))])
  rw [one_div, inv_le_inv₀ (by positivity) (by positivity)]
  exact mul_le_mul_of_nonneg_right (by linarith) hlog.le

/-- The quadratic good event gives the displayed square-root/logarithmic envelope. -/
theorem discrepancyProfile_lower_bound (x : ℤ) (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hx : |(x : ℝ)| ≤ C * ((j : ℝ) + 1) ^ 2) :
    shiftedLogWeight j /
      (Real.sqrt (C + 2) * (2 + Real.log (C + 2) / Real.log 2)) ≤
      discrepancyProfile x := by
  have hn : 1 ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have hC2 : 0 < C + 2 := by positivity
  have hx2 : 0 < 2 + |(x : ℝ)| := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : 0 ≤ Real.log (C + 2) := Real.log_nonneg (by linarith)
  have hlogx : 0 < Real.log (2 + |(x : ℝ)|) := Real.log_pos (by linarith [abs_nonneg (x : ℝ)])
  have harg : 2 + |(x : ℝ)| ≤ (C + 2) * ((j : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg ((j : ℝ) + 1), sq_nonneg (j : ℝ)]
  have hsqrt : Real.sqrt (2 + |(x : ℝ)|) ≤
      Real.sqrt (C + 2) * ((j : ℝ) + 1) := by
    calc
      _ ≤ Real.sqrt ((C + 2) * ((j : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt harg
      _ = _ := by rw [Real.sqrt_mul hC2.le, Real.sqrt_sq (by positivity)]
  have hlogbase : Real.log (2 + |(x : ℝ)|) ≤
      Real.log (C + 2) + 2 * Real.log ((j : ℝ) + 1) := by
    calc
      _ ≤ Real.log ((C + 2) * ((j : ℝ) + 1) ^ 2) := Real.log_le_log hx2 harg
      _ = _ := by rw [Real.log_mul hC2.ne' (by positivity), Real.log_pow]; norm_num
  have hlog2j : Real.log 2 ≤ Real.log ((j : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))])
  have hlogsucc : Real.log ((j : ℝ) + 1) ≤ Real.log ((j : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hratio := mul_le_mul_of_nonneg_left hlog2j (div_nonneg hlogC hlog2.le)
  rw [div_mul_cancel₀ _ hlog2.ne'] at hratio
  have hlog : Real.log (2 + |(x : ℝ)|) ≤
      (2 + Real.log (C + 2) / Real.log 2) * Real.log ((j : ℝ) + 2) := by
    nlinarith
  have hdenom : Real.sqrt (2 + |(x : ℝ)|) * Real.log (2 + |(x : ℝ)|) ≤
      (Real.sqrt (C + 2) * (2 + Real.log (C + 2) / Real.log 2)) *
        (((j : ℝ) + 1) * Real.log ((j : ℝ) + 2)) := by
    calc
      _ ≤ (Real.sqrt (C + 2) * ((j : ℝ) + 1)) *
          ((2 + Real.log (C + 2) / Real.log 2) * Real.log ((j : ℝ) + 2)) :=
        mul_le_mul hsqrt hlog hlogx.le (by positivity)
      _ = _ := by ring
  unfold shiftedLogWeight discrepancyProfile
  rw [div_div, mul_comm (((j : ℝ) + 1) * Real.log ((j : ℝ) + 2))]
  exact one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr hx2) hlogx) hdenom

/-- The original uniform quadratic marginal tail premise suffices without independence. -/
theorem ae_tsum_discrepancyProfile_eq_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Ω → ℤ)
    (hE : ∀ j, Measurable (E j))
    (htail : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ j : ℕ,
      μ {ω | C * ((j : ℝ) + 1) ^ 2 < |(E j ω : ℝ)|} ≤ ENNReal.ofReal δ) :
    ∀ᵐ ω ∂μ, ∑' j, ENNReal.ofReal (discrepancyProfile (E j ω)) = ∞ := by
  apply UniformLowerQuantileSeries.ae_tsum_eq_top_of_uniform_lower_quantiles μ
    (fun j ω => ENNReal.ofReal (discrepancyProfile (E j ω)))
    (fun j => ENNReal.ofReal (shiftedLogWeight j))
    (fun j => (measurable_of_countable
      (fun z : ℤ => ENNReal.ofReal (discrepancyProfile z))).comp (hE j))
    tsum_shiftedLogWeight_eq_top
  intro error herror
  obtain ⟨C, hC⟩ := htail (error : ℝ) (by exact_mod_cast herror)
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  let denominator : ℝ := Real.sqrt (B + 2) *
    (2 + Real.log (B + 2) / Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log (B + 2) := Real.log_nonneg (by linarith)
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    exact mul_pos (Real.sqrt_pos.mpr (by linarith))
      (by linarith [div_nonneg hlogB hlog2.le])
  let scale : ℝ≥0 := ⟨1 / denominator, (one_div_pos.mpr hdenominator).le⟩
  refine ⟨scale, ?_, ?_⟩
  · exact_mod_cast one_div_pos.mpr hdenominator
  · intro j
    calc
      μ {ω | ENNReal.ofReal (discrepancyProfile (E j ω)) <
          (scale : ℝ≥0∞) * ENNReal.ofReal (shiftedLogWeight j)} ≤
          μ {ω | C * ((j : ℝ) + 1) ^ 2 < |(E j ω : ℝ)|} := by
        apply measure_mono
        intro ω hω
        by_contra hbad
        have hgood : |(E j ω : ℝ)| ≤ B * ((j : ℝ) + 1) ^ 2 :=
          (le_of_not_gt hbad).trans
            (mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg _))
        have hlower := discrepancyProfile_lower_bound (E j ω) j B hB hgood
        have hscale : (scale : ℝ≥0∞) = ENNReal.ofReal (1 / denominator) := by
          rw [ENNReal.ofReal_eq_coe_nnreal (one_div_pos.mpr hdenominator).le]
          rfl
        have hlower' : (scale : ℝ≥0∞) * ENNReal.ofReal (shiftedLogWeight j) ≤
            ENNReal.ofReal (discrepancyProfile (E j ω)) := by
          rw [hscale, ← ENNReal.ofReal_mul (one_div_pos.mpr hdenominator).le]
          apply ENNReal.ofReal_le_ofReal
          simpa only [denominator, one_div, div_eq_mul_inv, mul_comm, one_mul] using hlower
        exact (not_lt_of_ge hlower') hω
      _ ≤ (error : ℝ≥0∞) := by simpa only [ENNReal.ofReal_coe_nnreal] using hC j

#print axioms tsum_shiftedLogWeight_eq_top
#print axioms discrepancyProfile_lower_bound
#print axioms ae_tsum_discrepancyProfile_eq_top

end D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
