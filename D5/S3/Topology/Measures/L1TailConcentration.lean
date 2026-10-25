/- GID: D5/S3/Topology/Measures/L1TailConcentration
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1TailConcentration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tail concentration with summably small effects on every earlier input. -/

import D5.S3.Topology.Measures.L1TailSelection
import D5.S3.Topology.Measures.L1Restriction
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Recursive hard tails with simultaneous limits and summable old-input losses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace D5.S3.Topology.Measures.L1TailConcentration

open L1Restriction

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Uniformly small hard-tail supports have arbitrarily small integrals for every finite prefix. -/
theorem eventually_small_cross_tails
    (f : ℕ → Lp ℝ 1 μ) (B : ℝ) (hb : ∀ n, ‖f n‖ ≤ B)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K in atTop, ∀ n, n ≤ N → ∀ m,
      ‖restrict (tailSet K (f m)) (measurable_tailSet K (f m)) (f n)‖ ≤ ε := by
  let F : Fin (N + 1) → Ω → ℝ := fun n => f n
  have hF : UnifIntegrable F 1 μ := unifIntegrable_finite (by norm_num) (by norm_num)
    (fun n => Lp.memLp (f n))
  obtain ⟨δ, hδ, hsmall⟩ := (unifIntegrable_iff.1 hF)
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  let D := ENNReal.ofReal B
  have hdlim : Tendsto (fun K : ℕ => D / K) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [eventually_gt_atTop 0, (tendsto_order.1 hdlim).2 δ hδ] with K hK hKd
  intro n hn m
  have hmass : (∫⁻ x, ‖f m x‖ₑ ∂μ) ≤ D := by
    rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable (f m)),
      ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb m)
  have hμ : μ (tailSet K (f m)) ≤ D / K := by
    have hmark := meas_ge_le_lintegral_div (Lp.aestronglyMeasurable (f m)).enorm
      (show (K : ℝ≥0∞) ≠ 0 by exact_mod_cast hK.ne') (ENNReal.natCast_ne_top K)
    have heq : {x | (K : ℝ≥0∞) ≤ ‖f m x‖ₑ} = tailSet K (f m) := by
      ext x
      rw [mem_setOf_eq, ← ofReal_norm, ENNReal.natCast_le_ofReal hK.ne']
      rfl
    rw [heq] at hmark
    exact hmark.trans (by gcongr)
  have hbound : eLpNorm ((tailSet K (f m)).indicator (f n)) 1 μ ≤ ENNReal.ofReal ε := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurable_tailSet K (f m)).nullMeasurableSet]
    exact hsmall ⟨n, by omega⟩ (tailSet K (f m)) (hμ.trans hKd.le)
  rw [L1Restriction.restrict, Lp.norm_toLp]
  simpa only [ENNReal.toReal_ofReal hε.le] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

/-- Hard-tail concentration on actual measurable superlevel sets. Each later
support has summably small integral for every earlier selected input. -/
theorem exists_tail_concentration (f : ℕ → Lp ℝ 1 μ)
    (B : ℝ) (hb : ∀ n, ‖f n‖ ≤ B) :
    ∃ (j K : ℕ → ℕ) (c : ℕ → ℝ) (α : ℝ),
      StrictMono j ∧ (∀ i, i < K i) ∧ 0 ≤ α ∧
      (∀ k, α ≤ c k) ∧ Tendsto c atTop (𝓝 α) ∧
      (∀ k, Tendsto (fun i => tailNorm k (f (j i))) atTop (𝓝 (c k))) ∧
      Tendsto (fun i => tailNorm (K i) (f (j i))) atTop (𝓝 α) ∧
      (∀ h i, h < i →
        ‖restrict (tailSet (K i) (f (j i))) (measurable_tailSet (K i) (f (j i))) (f (j h))‖ ≤
          (1 / 2 : ℝ) ^ i) := by
  let P (i N K : ℕ) := ∀ n, n ≤ N → ∀ m,
    ‖restrict (tailSet K (f m)) (measurable_tailSet K (f m)) (f n)‖ ≤ (1 / 2 : ℝ) ^ i
  have hp (i N : ℕ) : ∀ᶠ K in atTop, P i N K :=
    eventually_small_cross_tails f B hb N _ (by positivity)
  obtain ⟨j, K, c, α, N, hj, hK, hα, hαk, hc, hfixed, hmoving, hP, hN⟩ :=
    L1TailSelection.exists_selection (fun n k => tailNorm k (f n)) B
      (fun n k => ⟨norm_nonneg _, (norm_le _ _ _).trans (hb n)⟩)
      (fun n => tailNorm_antitone (f n)) P hp
  exact ⟨j, K, c, α, hj, hK, hα, hαk, hc, hfixed, hmoving,
    fun h i hhi => hP i (j h) (hN h i hhi) (j i)⟩

end D5.S3.Topology.Measures.L1TailConcentration
