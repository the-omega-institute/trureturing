/- GID: D5/S3/Analytic/PrimeProducts/GeometricResidualMemorylessness
   generality: G
   mirror-B: D5/B/S3/Analytic/PrimeProducts/GeometricResidualMemorylessness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditioning a geometric law on a tail preserves its translated residual law. -/

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic

/- Library-search audit trail (2026-08-26):
   * Pinned Mathlib supplies the exact canonical `geometricMeasure`, its
     singleton-mass theorem, conditional measures, measure pushforwards, and
     extensionality on singletons; all are used directly below.
   * Searches in pinned Mathlib and D5 found no theorem identifying a translated
     conditioned geometric measure with the original measure.
   * No new `def` or `abbrev` is introduced. The public statement constructs the
     conditioned residual law directly from the canonical measure primitives. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal ProbabilityTheory

noncomputable section

namespace D5.S3.Analytic.PrimeProducts.GeometricResidualMemorylessness

open MeasureTheory ProbabilityTheory Set

private lemma geometric_tail_mass (success : unitInterval)
    (success_ne_zero : success ≠ 0) (k : Nat) :
    geometricMeasure success (Set.Ici k) =
      ENNReal.ofReal ((1 - success : Real) ^ k) := by
  rw [← compl_Iio, prob_compl_eq_one_sub (measurableSet_Iio : MeasurableSet (Iio k))]
  rw [geometricMeasure_eq success_ne_zero,
    Measure.sum_apply _ (MeasurableSet.of_discrete (s := Iio k))]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.range k)]
  · simp_rw [Measure.dirac_apply' _ MeasurableSet.of_discrete]
    have indicator_sum :
        (∑ n ∈ Finset.range k,
            ENNReal.ofReal ((1 - success : Real) ^ n * success) *
              (Iio k).indicator 1 n) =
          ∑ n ∈ Finset.range k,
            ENNReal.ofReal ((1 - success : Real) ^ n * success) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Set.indicator_of_mem]
      · exact mul_one _
      · exact Finset.mem_range.mp hn
    rw [indicator_sum, ← ENNReal.ofReal_sum_of_nonneg]
    · have finite_mass_nonneg :
          0 ≤ ∑ n ∈ Finset.range k,
            (1 - success : Real) ^ n * success :=
        Finset.sum_nonneg fun n hn => geometricMeasure_nonneg success n
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 finite_mass_nonneg]
      congr 1
      have geometric_sum := geom_sum_mul_neg (1 - success : Real) k
      rw [← Finset.sum_mul]
      linarith
    · intro n hn
      exact geometricMeasure_nonneg success n
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    simp [Measure.dirac_apply' _ MeasurableSet.of_discrete, hn]

/-- For every nondegenerate zero-start geometric law, conditioning on the event
`V ≥ k` and translating by `k` gives back the original complete law. -/
theorem geometric_residual_memoryless (success : unitInterval)
    (success_ne_zero : success ≠ 0) (success_ne_one : success ≠ 1) (k : Nat) :
    Measure.map (fun value : Nat => value - k)
        ((geometricMeasure success)[| Set.Ici k]) =
      geometricMeasure success := by
  apply Measure.ext_of_singleton
  intro residual
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete]
  rw [cond_apply' MeasurableSet.of_discrete]
  have preimage_tail :
      Set.Ici k ∩ (fun value : Nat => value - k) ⁻¹' ({residual} : Set Nat) =
        {residual + k} := by
    ext value
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [preimage_tail, geometric_tail_mass success success_ne_zero k,
    geometricMeasure_singleton success_ne_zero,
    geometricMeasure_singleton success_ne_zero]
  have success_real_ne_one : (success : Real) ≠ 1 := by
    intro success_real_eq_one
    apply success_ne_one
    exact Subtype.ext success_real_eq_one
  have ratio_pos : 0 < (1 - success : Real) := by
    exact sub_pos.mpr (lt_of_le_of_ne success.2.2 success_real_ne_one)
  have factorization :
      (1 - success : Real) ^ (residual + k) * success =
        (1 - success : Real) ^ k *
          ((1 - success : Real) ^ residual * success) := by
    rw [pow_add]
    ring
  rw [factorization, ENNReal.ofReal_mul (pow_nonneg ratio_pos.le k), ← mul_assoc,
    ENNReal.inv_mul_cancel]
  · exact one_mul _
  · exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos ratio_pos k)
  · exact ENNReal.ofReal_ne_top

#print axioms geometric_residual_memoryless

end D5.S3.Analytic.PrimeProducts.GeometricResidualMemorylessness
