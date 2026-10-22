/- GID: D5/S3/Analytic/ExpRatioCM/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Refutation and exact low-index classification of exponential derivative ratios. -/

import D5.S3.Analytic.ExpRatioCM.Extraction
import D5.S3.Analytic.ExpRatioCM.Positive

/-! Refutation and low-index classification assembly. -/

open scoped Topology
open Filter
open D5.S3.Analytic.ExpRatioCM.Defs
open D5.S3.Analytic.ExpRatioCM.Extraction
open D5.S3.Analytic.ExpRatioCM.Positive
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

/-- The coefficient-extraction contradiction for either ratio family. -/
theorem not_cm_of_three_le
    (hlimF : ∀ i : ℕ, 3 ≤ i →
      Tendsto (fun k : ℕ =>
        (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k (ratioF i)
            (k * Real.log (7 / 4))))
        atTop (𝓝 (quotCoeff i 2)))
    (hlimG : ∀ i : ℕ, 3 ≤ i →
      Tendsto (fun k : ℕ =>
        (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k (ratioG i)
            (k * Real.log (7 / 4))))
        atTop (𝓝 (quotCoeff i 2))) :
    ∀ i : ℕ, 3 ≤ i →
      ¬ CompletelyMonotoneOn (ratioF i) ∧
      ¬ CompletelyMonotoneOn (ratioG i) := by
  intro i hi
  have hb : quotCoeff i 2 < 0 := by
    rw [quotCoeff_two]
    exact coeff_two_negative hi
  exact ⟨not_completelyMonotone_of_extraction (hlimF i hi) hb,
    not_completelyMonotone_of_extraction (hlimG i hi) hb⟩

/-- Combining positive low-index coefficient data with the failure family. -/
theorem classification_of_limits
    (hlimF : ∀ i : ℕ, 3 ≤ i →
      Tendsto (fun k : ℕ =>
        (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k (ratioF i)
            (k * Real.log (7 / 4))))
        atTop (𝓝 (quotCoeff i 2)))
    (hlimG : ∀ i : ℕ, 3 ≤ i →
      Tendsto (fun k : ℕ =>
        (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k (ratioG i)
            (k * Real.log (7 / 4))))
        atTop (𝓝 (quotCoeff i 2)))
    (hpositive : ∀ i : ℕ, i ≤ 2 →
      CompletelyMonotoneOn (ratioF i) ∧
      CompletelyMonotoneOn (ratioG i)) :
    (∀ i : ℕ, CompletelyMonotoneOn (ratioF i) ↔ i ≤ 2) ∧
      (∀ i : ℕ, CompletelyMonotoneOn (ratioG i) ↔ i ≤ 2) := by
  have hfail := not_cm_of_three_le hlimF hlimG
  constructor
  · intro i
    constructor
    · intro h
      by_contra hnot
      have hi : 3 ≤ i := by omega
      exact hfail i hi |>.1 h
    · intro hi
      exact (hpositive i hi).1
  · intro i
    constructor
    · intro h
      by_contra hnot
      have hi : 3 ≤ i := by omega
      exact hfail i hi |>.2 h
    · intro hi
      exact (hpositive i hi).2

/-- The conjecture is refuted once the extracted limits and positive cases are supplied. -/
theorem result_of_limits
    (hlimF : ∀ i : ℕ, 3 ≤ i →
      Tendsto (fun k : ℕ =>
        (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k (ratioF i)
            (k * Real.log (7 / 4))))
        atTop (𝓝 (quotCoeff i 2)))
    (hlimG : ∀ i : ℕ, 3 ≤ i →
      Tendsto (fun k : ℕ =>
        (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k (ratioG i)
            (k * Real.log (7 / 4))))
        atTop (𝓝 (quotCoeff i 2)))
    (hpositive : ∀ i : ℕ, i ≤ 2 →
      CompletelyMonotoneOn (ratioF i) ∧
      CompletelyMonotoneOn (ratioG i)) :
    ¬ claim := by
  intro hclaim
  obtain ⟨hF, _hG⟩ := hclaim 3
  have hfail := not_cm_of_three_le hlimF hlimG
  exact (hfail 3 (by norm_num)).1 hF

end D5.S3.Analytic.ExpRatioCM.Result
