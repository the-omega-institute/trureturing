/- GID: D5/S3/Analytic/ExpRatioCM/Extraction
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Extraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extraction of a distinguished exponential coefficient from scaled derivative values. -/

import D5.S3.Analytic.ExpRatioCM.Series

/-! Coefficient extraction from scaled alternating derivatives. -/

open scoped BigOperators Topology
open Filter
open D5.S3.Analytic.ExpRatioCM.Defs

open D5.S3.Analytic.ExpRatioCM.Series

noncomputable section
namespace D5.S3.Analytic.ExpRatioCM.Extraction

/-- A vanishing tail leaves the second exponential coefficient after scaling. -/
theorem extraction_limit {b r : ℕ → ℝ} {h : ℝ → ℝ}
    (hmain : ∀ᶠ k : ℕ in atTop,
      (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))) =
        b 2 + r k)
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k : ℕ =>
      (49 / 32 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))))
      atTop (𝓝 (b 2)) := by
  have hlim : Tendsto (fun k : ℕ => b 2 + r k) atTop (𝓝 (b 2 + 0)) := by
    simpa using (tendsto_const_nhds.add hr)
  have hlim' : Tendsto (fun k : ℕ => b 2 + r k) atTop (𝓝 (b 2)) := by
    simpa using hlim
  apply hlim'.congr'
  filter_upwards [hmain] with k hk
  exact hk.symm

private def extractionWeight (n : ℕ) : ℝ :=
  (49 / 32 : ℝ) * n * (4 / 7 : ℝ) ^ n

private lemma weight_nonneg (n : ℕ) : 0 ≤ extractionWeight n := by
  dsimp [extractionWeight]; positivity

private lemma weight_tail (n : ℕ) :
    extractionWeight (n + 3) ≤ (6 / 7 : ℝ) * (16 / 21 : ℝ) ^ n := by
  have hstep (j : ℕ) : extractionWeight (j + 3 + 1) ≤
      (16 / 21 : ℝ) * extractionWeight (j + 3) := by
    dsimp [extractionWeight]
    rw [pow_succ]
    push_cast
    have hp : 0 ≤ (4 / 7 : ℝ) ^ (j + 3) := by positivity
    nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hp]
  have h := le_geom (u := fun n => extractionWeight (n + 3))
    (by norm_num : (0 : ℝ) ≤ 16 / 21) n (fun j _ => hstep j)
  norm_num [extractionWeight] at h ⊢
  simpa only [mul_comm] using h

private lemma tail_term_bound {b : ℕ → ℝ} {B : ℝ}
    (hB : 0 < B) (hb : ∀ n, |b n| ≤ B ^ n) (k n : ℕ)
    (hk : B * (16 / 21 : ℝ) ^ k ≤ 1 / 2) :
    ‖b (n + 3) * extractionWeight (n + 3) ^ k‖ ≤
      (B ^ 3 * (6 / 7 : ℝ) ^ k) * (1 / 2 : ℝ) ^ n := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (weight_nonneg _) _)]
  calc
    _ ≤ B ^ (n + 3) * ((6 / 7 : ℝ) * (16 / 21 : ℝ) ^ n) ^ k :=
      mul_le_mul (hb _) (pow_le_pow_left₀ (weight_nonneg _) (weight_tail n) k)
        (pow_nonneg (weight_nonneg _) _) (by positivity)
    _ = (B ^ 3 * (6 / 7 : ℝ) ^ k) * (B * (16 / 21 : ℝ) ^ k) ^ n := by
      rw [pow_add, mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n k]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hk n) (by positivity)

private lemma normalized_series_bound {b : ℕ → ℝ} {B : ℝ}
    (hB : 0 < B) (hb : ∀ n, |b n| ≤ B ^ n) {k : ℕ} (hk0 : 1 ≤ k)
    (hk : B * (16 / 21 : ℝ) ^ k ≤ 1 / 2) :
    |(∑' n : ℕ, b n * extractionWeight n ^ k) - b 2| ≤
      |b 1| * (7 / 8 : ℝ) ^ k + 2 * B ^ 3 * (6 / 7 : ℝ) ^ k := by
  have hs := ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).mul_left (B ^ 3 * (6 / 7 : ℝ) ^ k))
  have htail : Summable (fun n : ℕ => ‖b (n + 3) * extractionWeight (n + 3) ^ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (tail_term_bound hB hb k · hk) hs
  have hall : Summable (fun n : ℕ => b n * extractionWeight n ^ k) :=
    (summable_nat_add_iff 3).mp htail.of_norm
  have hsplit := hall.sum_add_tsum_nat_add 3
  have hzero : extractionWeight 0 ^ k = 0 := by
    simp [extractionWeight, ne_of_gt (show 0 < k by omega)]
  have hone : extractionWeight 1 = 7 / 8 := by norm_num [extractionWeight]
  have htwo : extractionWeight 2 = 1 := by norm_num [extractionWeight]
  have hsplit' : (∑' n : ℕ, b n * extractionWeight n ^ k) - b 2 =
      b 1 * (7 / 8 : ℝ) ^ k + ∑' n : ℕ, b (n + 3) * extractionWeight (n + 3) ^ k := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hzero, hone, htwo,
      mul_zero, one_pow, mul_one, zero_add] at hsplit
    linarith [hsplit]
  rw [hsplit']
  calc
    _ ≤ |b 1 * (7 / 8 : ℝ) ^ k| + |∑' n : ℕ, b (n + 3) * extractionWeight (n + 3) ^ k| := abs_add_le _ _
    _ ≤ |b 1| * (7 / 8 : ℝ) ^ k +
        ∑' n : ℕ, (B ^ 3 * (6 / 7 : ℝ) ^ k) * (1 / 2 : ℝ) ^ n := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 8) _)]
      · exact (norm_tsum_le_tsum_norm htail).trans
          (htail.tsum_le_tsum (tail_term_bound hB hb k · hk) hs)
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
      ring

private lemma normalized_term (n k : ℕ) :
    (49 / 32 : ℝ) ^ k * ((n : ℝ) ^ k *
      Real.exp (-(n : ℝ) * ((k : ℝ) * Real.log (7 / 4)))) =
      extractionWeight n ^ k := by
  have he : Real.exp (-Real.log (7 / 4)) = (4 / 7 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 7 / 4)]
    norm_num
  have hn : Real.exp (-(n : ℝ) * ((k : ℝ) * Real.log (7 / 4))) =
      ((4 / 7 : ℝ) ^ n) ^ k := by
    rw [← he, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hn]
  simp only [extractionWeight, mul_pow]
  ring

/-- The actual quotient derivatives extract the second quotient coefficient. -/
theorem quotient_extraction_limit (i : ℕ) :
    Tendsto (fun k : ℕ => (49 / 32 : ℝ) ^ k *
      ((-1 : ℝ) ^ k * iteratedDeriv k (ratioF i) (k * Real.log (7 / 4))))
      atTop (𝓝 (quotCoeff i 2)) := by
  let B : ℝ := (2 : ℝ) ^ (i + 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hb : ∀ n, |quotCoeff i n| ≤ B ^ n := abs_quotCoeff_le i
  have hsmall : ∀ᶠ k : ℕ in atTop, B * (16 / 21 : ℝ) ^ k ≤ 1 / 2 := by
    have hlim : Tendsto (fun k : ℕ => B * (16 / 21 : ℝ) ^ k) atTop (𝓝 (B * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    exact (hlim.eventually (gt_mem_nhds (by norm_num : B * 0 < (1 / 2 : ℝ)))).mono (fun _ h => h.le)
  have hr : Tendsto (fun k : ℕ =>
      (∑' n : ℕ, quotCoeff i n * extractionWeight n ^ k) - quotCoeff i 2)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun k => abs_nonneg _))
    · filter_upwards [eventually_ge_atTop 1, hsmall] with k hk0 hk
      exact normalized_series_bound hB hb hk0 hk
    · have h₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num)).const_mul |quotCoeff i 1|
      have h₂ := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 6 / 7) (by norm_num)).const_mul (2 * B ^ 3)
      simpa using h₁.add h₂
  apply extraction_limit (b := quotCoeff i) (r := fun k =>
    (∑' n : ℕ, quotCoeff i n * extractionWeight n ^ k) - quotCoeff i 2) ?_ hr
  have ht : ∀ᶠ k : ℕ in atTop, Real.log B < (k : ℝ) * Real.log (7 / 4) :=
    (Tendsto.atTop_mul_const (Real.log_pos (by norm_num)) tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (Real.log B))
  filter_upwards [ht, eventually_ge_atTop 1] with k hkt hk
  rw [iteratedDeriv_ratioF i k hk hkt, ← tsum_mul_left]
  have heq : (∑' n : ℕ, (49 / 32 : ℝ) ^ k *
      (quotCoeff i n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * (k * Real.log (7 / 4))))) =
      ∑' n : ℕ, quotCoeff i n * extractionWeight n ^ k := by
    apply tsum_congr
    intro n
    rw [show (49 / 32 : ℝ) ^ k * (quotCoeff i n * (n : ℝ) ^ k *
        Real.exp (-(n : ℝ) * (k * Real.log (7 / 4)))) =
      quotCoeff i n * ((49 / 32 : ℝ) ^ k * ((n : ℝ) ^ k *
        Real.exp (-(n : ℝ) * (k * Real.log (7 / 4))))) by ring,
      normalized_term]
  rw [heq]
  ring

end D5.S3.Analytic.ExpRatioCM.Extraction
