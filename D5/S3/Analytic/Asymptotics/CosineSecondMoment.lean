/- GID: D5/S3/Analytic/Asymptotics/CosineSecondMoment
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/CosineSecondMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A divergent second moment forces the normalized cosine defect to diverge. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Divergence of the normalized cosine defect

A divergent second moment of nonnegative summable weights forces the weighted
cosine defect divided by the squared displacement to tend to infinity at zero.
-/

open Filter
open scoped BigOperators Topology

namespace CosineSecondMoment

/-- A nonnegative summable weight with divergent second moment forces the
cosine defect divided by the square of the displacement to diverge at zero. -/
theorem tendsto_cosine_defect_div_sq_atTop (a ω : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hm : ¬ Summable (fun n => a n * (ω n) ^ 2)) :
    Tendsto (fun h : ℝ => (∑' n, a n * (1 - Real.cos (ω n * h))) / h ^ 2)
      (𝓝[≠] 0) atTop := by
  have hnonneg (h : ℝ) (n : ℕ) : 0 ≤ a n * (1 - Real.cos (ω n * h)) :=
    mul_nonneg (ha n) (sub_nonneg.mpr (Real.cos_le_one _))
  have hsummable (h : ℝ) : Summable (fun n => a n * (1 - Real.cos (ω n * h))) := by
    refine Summable.of_nonneg_of_le (hnonneg h) ?_ (hs.mul_left 2)
    intro n
    calc
      a n * (1 - Real.cos (ω n * h)) ≤ a n * (1 - (-1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left (Real.neg_one_le_cos _) 1) (ha n)
      _ = 2 * a n := by ring
  let c : ℝ := 2 / Real.pi ^ 2
  have hc : 0 < c := div_pos two_pos (pow_pos Real.pi_pos 2)
  have hpartial := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => mul_nonneg (ha n) (sq_nonneg (ω n)))).mp hm
  refine tendsto_atTop.2 fun B => ?_
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 hpartial (B / c)).exists
  have hB : B ≤ c * (∑ n ∈ Finset.range N, a n * (ω n) ^ 2) :=
    (div_le_iff₀' hc).mp hN
  have hsmall : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), ∀ n ∈ Finset.range N, |ω n * h| ≤ Real.pi := by
    refine (eventually_all_finset (Finset.range N)).2 fun n _ => ?_
    have hcont : ContinuousAt (fun h : ℝ => |ω n * h|) 0 :=
      ((continuous_const : Continuous (fun _ : ℝ => ω n)).mul continuous_id).abs.continuousAt
    have hlt : |ω n * (0 : ℝ)| < Real.pi := by simpa using Real.pi_pos
    exact (hcont.eventually_lt continuousAt_const hlt).mono fun _ hx => hx.le
  refine eventually_nhdsWithin_iff.mpr (hsmall.mono ?_)
  intro h hh hmem
  have hne : h ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  have hh2 : 0 < h ^ 2 := sq_pos_of_ne_zero hne
  calc
    B ≤ c * (∑ n ∈ Finset.range N, a n * (ω n) ^ 2) := hB
    _ = ∑ n ∈ Finset.range N, c * (a n * (ω n) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.range N, (a n * (1 - Real.cos (ω n * h))) / h ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hcos : c * (ω n * h) ^ 2 ≤ 1 - Real.cos (ω n * h) :=
        le_sub_comm.mp (Real.cos_le_one_sub_mul_cos_sq (hh n hn))
      apply (le_div_iff₀ hh2).2
      calc
        c * (a n * (ω n) ^ 2) * h ^ 2 = a n * (c * (ω n * h) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcos (ha n)
    _ = (∑ n ∈ Finset.range N, a n * (1 - Real.cos (ω n * h))) / h ^ 2 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ _ := div_le_div_of_nonneg_right
      ((hsummable h).sum_le_tsum (Finset.range N) (fun n _ => hnonneg h n)) hh2.le

end CosineSecondMoment
