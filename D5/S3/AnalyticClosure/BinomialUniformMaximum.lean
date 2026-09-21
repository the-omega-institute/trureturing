/- GID: D5/S3/AnalyticClosure/BinomialUniformMaximum
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialUniformMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp eventual Gaussian upper bound at every binomial index. -/

import D5.S3.AnalyticClosure.BinomialLocalGaussian

open Filter Real Finset
open scoped Topology
open D5.S3.AnalyticClosure.BinomialLocalGaussian

namespace D5.S3.AnalyticClosure.BinomialUniformMaximum

/-- A sharp upper bound uniform over the whole support, without locating a mode.
Inside the local Gaussian window the exponential correction is at least one;
outside it a single mass is bounded by the entire scaled tail. -/
theorem uniform_upper (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ n →
      binomialMass p n k * sqrt (2 * π * n * p * (1 - p)) ≤ 1 + ε := by
  let C := 2 * π * p * (1 - p)
  have hC : 0 < C := by dsimp [C]; positivity
  let T (n : ℕ) := ∑ i ∈ (range (n + 1)).filter
    (fun i : ℕ => (n : ℝ) ^ (7 / 12 : ℝ) < |(i : ℝ) - n * p|),
    binomialMass p n i
  have htail : Tendsto (fun n : ℕ =>
      T n * sqrt (2 * π * n * p * (1 - p))) atTop (𝓝 0) := by
    have ht := (binomial_power_tail p hp hp1 1 (by omega) (1 / 2)).const_mul (sqrt C)
    simp only [mul_zero, pow_one] at ht
    apply ht.congr'
    filter_upwards with n
    have hid : 2 * π * (n : ℝ) * p * (1 - p) = C * n := by dsimp [C]; ring
    rw [hid, sqrt_mul hC.le, sqrt_eq_rpow (n : ℝ)]
    dsimp [T]
    ring
  obtain ⟨N, hN⟩ := local_gaussian_window p hp hp1 ε hε
  have hsmall := htail.eventually (gt_mem_nhds (show (0 : ℝ) < 1 + ε by positivity))
  filter_upwards [eventually_ge_atTop N, hsmall] with n hn ht k hk
  have hmass0 (i : ℕ) : 0 ≤ binomialMass p n i := by
    unfold binomialMass
    positivity
  by_cases hw : |(k : ℝ) - n * p| ≤ (n : ℝ) ^ (7 / 12 : ℝ)
  · have hlocal := (abs_lt.mp (hN n hn k hw)).2
    have he : 1 ≤ exp (((k : ℝ) - n * p) ^ 2 / (2 * n * p * (1 - p))) := by
      apply one_le_exp_iff.mpr
      positivity
    have hle := le_mul_of_one_le_right
      (mul_nonneg (hmass0 k) (sqrt_nonneg (2 * π * n * p * (1 - p)))) he
    linarith
  · have hsingle : binomialMass p n k ≤ T n := by
      apply single_le_sum (fun i _ => hmass0 i)
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hk), lt_of_not_ge hw⟩
    exact (mul_le_mul_of_nonneg_right hsingle (sqrt_nonneg _)).trans ht.le

end D5.S3.AnalyticClosure.BinomialUniformMaximum
