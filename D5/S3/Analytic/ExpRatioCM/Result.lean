/- GID: D5/S3/Analytic/ExpRatioCM/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Refutation and exact low-index classification of exponential derivative ratios. -/

import D5.S3.Analytic.ExpRatioCM.Extraction

/-! Refutation assembly. -/

open scoped Topology
open Filter
open D5.S3.Analytic.ExpRatioCM.Defs
open D5.S3.Analytic.ExpRatioCM.Extraction
open D5.S3.Analytic.ExpRatioCM.Series

namespace D5.S3.Analytic.ExpRatioCM.Result

private lemma coeff_two_negative {i : ℕ} (hi : 3 ≤ i) :
    2 * (3 : ℝ) ^ i - (4 : ℝ) ^ i < 0 := by
  have hp : ∀ j : ℕ, 3 ≤ j → 2 * (3 : ℝ) ^ j < (4 : ℝ) ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
        rw [pow_succ, pow_succ]
        have h₁ : 2 * (3 : ℝ) ^ j * 3 < (4 : ℝ) ^ j * 3 :=
          mul_lt_mul_of_pos_right ih (by norm_num)
        have h₂ : (4 : ℝ) ^ j * 3 < (4 : ℝ) ^ j * 4 := by
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) j]
        nlinarith [h₁, h₂]
  linarith [hp i hi]

/-- Both ratio families have a negative alternating derivative arbitrarily far to the right. -/
theorem failure_on_every_tail (i : ℕ) (hi : 3 ≤ i) (T : ℝ) :
    ∃ (k : ℕ) (t : ℝ), T < t ∧ 0 < t ∧
      (-1 : ℝ) ^ k * iteratedDeriv k (ratioF i) t < 0 ∧
      (-1 : ℝ) ^ k * iteratedDeriv k (ratioG i) t < 0 := by
  have hb : quotCoeff i 2 < 0 := by
    rw [quotCoeff_two]
    exact coeff_two_negative hi
  have hneg : ∀ᶠ k : ℕ in atTop, (49 / 32 : ℝ) ^ k *
      ((-1 : ℝ) ^ k * iteratedDeriv k (ratioF i) (k * Real.log (7 / 4))) < 0 :=
    (quotient_extraction_limit i).eventually (gt_mem_nhds hb)
  have ht : Tendsto (fun k : ℕ => (k : ℝ) * Real.log (7 / 4)) atTop atTop :=
    Tendsto.atTop_mul_const (Real.log_pos (by norm_num)) tendsto_natCast_atTop_atTop
  obtain ⟨k, hk, hkT, hk0⟩ := (hneg.and ((ht.eventually (eventually_gt_atTop T)).and
    (ht.eventually (eventually_gt_atTop 0)))).exists
  have hd : (-1 : ℝ) ^ k * iteratedDeriv k (ratioF i) (k * Real.log (7 / 4)) < 0 := by
    have hp : 0 < (49 / 32 : ℝ) ^ k := by positivity
    by_contra hn
    exact (not_le_of_gt hk) (mul_nonneg hp.le (le_of_not_gt hn))
  refine ⟨k, k * Real.log (7 / 4), hkT, hk0, hd, ?_⟩
  have he : ratioG i =ᶠ[𝓝 ((k : ℝ) * Real.log (7 / 4))] ratioF i := by
    filter_upwards [Ioi_mem_nhds hk0] with t ht
    exact ratioG_eq_ratioF (by omega) ht
  rw [he.iteratedDeriv_eq k]
  exact hd

/-- The universal assertion about consecutive signed derivative ratios is false. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨k, t, hT, ht, hF, hG⟩ := failure_on_every_tail 3 le_rfl 0
  have hnonneg := add_nonneg ((hclaim 3).1.2 k t hT) ((hclaim 3).2.2 k t ht)
  exact (not_le_of_gt (add_neg hF hG)) hnonneg

end D5.S3.Analytic.ExpRatioCM.Result
