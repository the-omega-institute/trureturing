/- GID: D5/S3/TotalVariation/DataProcessing
   generality: G
   mirror-B: D5/B/S3/TotalVariation/DataProcessing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove contraction of finite total variation under a stochastic channel. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `totalVariation`, `total variation`,
     `data processing`, `Markov`, `stochastic`, `L¹`, `contraction`,
     `abs_sum_le_sum_abs`, `norm_sum_le`, and `bayesRisk_le_bayesRisk_comp`.
   * No finite-real total-variation DPI or L¹-contraction theorem for stochastic matrices was
     found. Mathlib's total variations are measure-valued, and its Bayes-risk DPI is stated for
     measure-theoretic kernels. The scalar finite-sum lemma `Finset.abs_sum_le_sum_abs` is reused.
   * Repository grep over every Lean declaration below `D5/S3` found the finite-real total
     variation and KL channel inequalities, but no total-variation channel inequality under
     another name. The sibling metric file at commit `30cf12c1` likewise contains no such result.
-/

import D5.S3.TotalVariation.Pinsker

namespace D5.S3.TotalVariation.DataProcessing

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker

/-- A nonnegative row-stochastic finite channel contracts total variation. The input functions
are arbitrary real functions; neither nonnegativity nor normalization of `p` and `q` is needed. -/
theorem total_variation_channel_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    totalVariation (channelOutput W p) (channelOutput W q) ≤ totalVariation p q := by
  classical
  rw [totalVariation, totalVariation]
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc
    (∑ y, |channelOutput W p y - channelOutput W q y|) =
        ∑ y, |∑ x, (p x - q x) * W x y| := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      rw [channelOutput, channelOutput, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ y, ∑ x, |(p x - q x) * W x y| := by
      apply Finset.sum_le_sum
      intro y _
      simpa using Finset.abs_sum_le_sum_abs
        (fun x => (p x - q x) * W x y) Finset.univ
    _ = ∑ y, ∑ x, |p x - q x| * W x y := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hW.1 x y)]
    _ = ∑ x, ∑ y, |p x - q x| * W x y := Finset.sum_comm
    _ = ∑ x, |p x - q x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, hW.2 x, mul_one]

end D5.S3.TotalVariation.DataProcessing
