/- GID: D5/S0/Asymptotics/WeightedProbability/UniformLowerQuantileSeries
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/UniformLowerQuantileSeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform lower quantiles force nonnegative series to diverge almost everywhere. -/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
This is an unbounded symbolic theorem for arbitrary finite measure spaces and
countably many measurable functions. It is not a bounded enumeration, checker,
numeric reduction, or certified finite instance.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.UniformLowerQuantileSeries

theorem ae_tsum_eq_top_of_uniform_lower_quantiles {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (values : ℕ → Ω → ℝ≥0∞) (weights : ℕ → ℝ≥0∞)
    (hmeasurable : ∀ index, Measurable (values index))
    (hweights : ∑' index, weights index = ∞)
    (hquantile : ∀ error : ℝ≥0, 0 < error →
      ∃ scale : ℝ≥0, 0 < scale ∧ ∀ index,
        μ {sample | values index sample < (scale : ℝ≥0∞) * weights index} ≤ error) :
    ∀ᵐ sample ∂μ, ∑' index, values index sample = ∞ := by
  classical
  let total : Ω → ℝ≥0∞ := fun sample => ∑' index, values index sample
  have htotal_measurable : Measurable total := Measurable.tsum hmeasurable
  have hbounded_null : ∀ bound : ℕ, μ {sample | total sample ≤ bound} = 0 := by
    intro bound
    let bounded : Set Ω := {sample | total sample ≤ bound}
    have hbounded : MeasurableSet bounded := measurableSet_le htotal_measurable measurable_const
    by_contra hnonzero
    have hmeasure_pos : 0 < (μ bounded).toNNReal :=
      ENNReal.toNNReal_pos hnonzero (measure_ne_top μ bounded)
    let error : ℝ≥0 := (μ bounded).toNNReal / 2
    have herror : 0 < error := div_pos hmeasure_pos (by norm_num)
    obtain ⟨scale, hscale, htail⟩ := hquantile error herror
    have hhalves : (error : ℝ≥0∞) + error = μ bounded := by
      rw [← ENNReal.coe_add]
      change (((μ bounded).toNNReal / 2 + (μ bounded).toNNReal / 2 : ℝ≥0) : ℝ≥0∞) = _
      rw [add_halves, ENNReal.coe_toNNReal (measure_ne_top μ bounded)]
    have hlower : ∀ index,
        (scale : ℝ≥0∞) * weights index * error ≤
          ∫⁻ sample, bounded.indicator (values index) sample ∂μ := by
      intro index
      let good : Set Ω := {sample | (scale : ℝ≥0∞) * weights index ≤ values index sample}
      have hgood : MeasurableSet good := measurableSet_le measurable_const (hmeasurable index)
      have hbad : μ (bounded \ good) ≤ (error : ℝ≥0∞) := by
        apply le_trans (measure_mono ?_) (htail index)
        intro sample hsample
        have hnot : ¬(scale : ℝ≥0∞) * weights index ≤ values index sample := hsample.2
        exact lt_of_not_ge hnot
      have hinter : (error : ℝ≥0∞) ≤ μ (bounded ∩ good) := by
        apply ENNReal.le_of_add_le_add_right (by simp : (error : ℝ≥0∞) ≠ ∞)
        calc
          (error : ℝ≥0∞) + error = μ bounded := hhalves
          _ = μ (bounded ∩ good) + μ (bounded \ good) :=
            (measure_inter_add_sdiff bounded hgood).symm
          _ ≤ μ (bounded ∩ good) + error := add_le_add le_rfl hbad
      calc
        (scale : ℝ≥0∞) * weights index * error ≤
            (scale : ℝ≥0∞) * weights index * μ (bounded ∩ good) :=
          mul_le_mul le_rfl hinter bot_le bot_le
        _ = ∫⁻ sample, (bounded ∩ good).indicator
              (fun _ => (scale : ℝ≥0∞) * weights index) sample ∂μ :=
          (lintegral_indicator_const (hbounded.inter hgood) _).symm
        _ ≤ ∫⁻ sample, bounded.indicator (values index) sample ∂μ := by
          apply lintegral_mono
          intro sample
          by_cases hsample : sample ∈ bounded ∩ good
          · rw [indicator_of_mem hsample, indicator_of_mem hsample.1]
            exact hsample.2
          · rw [indicator_of_notMem hsample]
            exact bot_le
    have hrestricted :
        (∫⁻ sample, bounded.indicator total sample ∂μ) =
          ∑' index, ∫⁻ sample, bounded.indicator (values index) sample ∂μ := by
      have hindicator : bounded.indicator total =
          fun sample => ∑' index, bounded.indicator (values index) sample := by
        funext sample
        by_cases hsample : sample ∈ bounded <;> simp [hsample, total]
      rw [hindicator, lintegral_tsum]
      intro index
      exact ((hmeasurable index).indicator hbounded).aemeasurable
    have hupper : (∫⁻ sample, bounded.indicator total sample ∂μ) ≤
        (bound : ℝ≥0∞) * μ bounded := by
      rw [← lintegral_indicator_const hbounded (bound : ℝ≥0∞)]
      apply lintegral_mono
      intro sample
      by_cases hsample : sample ∈ bounded
      · rw [indicator_of_mem hsample, indicator_of_mem hsample]
        exact hsample
      · rw [indicator_of_notMem hsample, indicator_of_notMem hsample]
    have hdiverges : ∑' index, (scale : ℝ≥0∞) * weights index * error = ∞ := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hweights]
      simp [ne_of_gt hscale, ne_of_gt herror]
    have htop : ∞ ≤ ∫⁻ sample, bounded.indicator total sample ∂μ := by
      rw [hrestricted, ← hdiverges]
      exact ENNReal.tsum_le_tsum hlower
    exact (not_le_of_gt (ENNReal.mul_lt_top (by simp) (measure_lt_top μ bounded)))
      (htop.trans hupper)
  rw [ae_iff]
  apply measure_mono_null ?_ (measure_iUnion_null hbounded_null)
  intro sample hsample
  obtain ⟨bound, hbound⟩ := ENNReal.exists_nat_gt hsample
  exact mem_iUnion.mpr ⟨bound, hbound.le⟩

#print axioms ae_tsum_eq_top_of_uniform_lower_quantiles

end D5.S0.Asymptotics.WeightedProbability.UniformLowerQuantileSeries
