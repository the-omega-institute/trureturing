/- GID: D5/S3/ArithSums/GiniMeanEndpointComparison
   generality: I
   mirror-B: D5/B/S3/ArithSums/GiniMeanEndpointComparison
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithSums/GiniMeanEndpointComparison.claim; result=D5/S3/ArithSums/GiniMeanEndpointComparison.result; claim=D5/S3/ArithSums/GiniMeanEndpointComparison.claim
   digest: A three-point rational witness refutes endpoint characterization of Gini mean comparisons. -/

/- Source: Grünwald–Páles, arXiv:2408.07658, §4, Conjecture 1.
   admission_basis: open-problem-resolution (#15731; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Definitions:
     giniMean: proof_shape definition; consumers=claim, gini_low_rs, gini_low_pq, gini_high_rs, gini_high_pq, gini_x_rs, gini_x_pq, nonneg_low_rs, nonneg_low_pq, nonneg_high_rs, nonneg_high_pq, nonneg_x_rs
     lowTuple: proof_shape definition; consumers=claim, gini_low_rs, gini_low_pq, nonneg_low_rs, nonneg_low_pq, result
     highTuple: proof_shape definition; consumers=claim, gini_high_rs, gini_high_pq, nonneg_high_rs, nonneg_high_pq, result
     claim: proof_shape definition; consumer=result
     x: proof_shape definition; consumers=gini_x_rs, gini_x_pq, nonneg_x_rs, result
   Per-declaration proof_shape and live consumers:
     gini_low_rs: bind-only; consumer=result
     gini_low_pq: bind-only; consumer=result
     gini_high_rs: bind-only; consumer=result
     gini_high_pq: bind-only; consumer=result
     gini_x_rs: bind-only; consumer=result
     gini_x_pq: bind-only; consumer=result
     le_fourth: bind-only; consumer=result
     nonneg_low_rs: bind-only; consumer=result
     nonneg_low_pq: bind-only; consumer=result
     nonneg_high_rs: bind-only; consumer=result
     nonneg_high_pq: bind-only; consumer=result
     nonneg_x_rs: bind-only; consumer=result
     result: bind-only; designated refutation conclusion
   The exact n=3, a=1, b=3 witness satisfies both endpoint tests while x=(1,1,5/3) reverses the comparison. -/

import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace D5.S3.ArithSums.GiniMeanEndpointComparison

/-- The Gini mean `G_{r,s}` of `x : Fin n → ℝ` for `r ≠ s`. -/
noncomputable def giniMean {n : ℕ} (r s : ℝ) (x : Fin n → ℝ) : ℝ :=
  ((∑ i, x i ^ r) / (∑ i, x i ^ s)) ^ (1 / (r - s))

/-- The tuple `(a, …, a, b)`. -/
def lowTuple (n : ℕ) (a b : ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) + 1 = n then b else a

/-- The tuple `(a, b, …, b)`. -/
def highTuple (n : ℕ) (a b : ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) = 0 then a else b

/-- The `⊇` direction of Conjecture 1 (for `r ≠ s`, `p ≠ q`, `I = [a, b]`). -/
def claim : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ a b : ℝ, 0 < a → a < b →
    ∀ r s p q : ℝ, r ≠ s → p ≠ q → r + s ≤ p + q →
      giniMean r s (lowTuple n a b) ≤ giniMean p q (lowTuple n a b) →
      giniMean r s (highTuple n a b) ≤ giniMean p q (highTuple n a b) →
        ∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc a b) → giniMean r s x ≤ giniMean p q x

private def x : Fin 3 → ℝ := ![1, 1, 5 / 3]

private lemma gini_low_rs :
    giniMean 3 (-1) (lowTuple 3 1 3) ^ (4 : ℕ) = 87 / 7 := by
  rw [giniMean]
  simp [lowTuple, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

private lemma gini_low_pq :
    giniMean 0 2 (lowTuple 3 1 3) ^ (4 : ℕ) = 121 / 9 := by
  rw [giniMean]
  simp [lowTuple, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg]

private lemma gini_high_rs :
    giniMean 3 (-1) (highTuple 3 1 3) ^ (4 : ℕ) = 33 := by
  rw [giniMean]
  simp [highTuple, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

private lemma gini_high_pq :
    giniMean 0 2 (highTuple 3 1 3) ^ (4 : ℕ) = 361 / 9 := by
  rw [giniMean]
  simp [highTuple, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg]

private lemma gini_x_rs : giniMean 3 (-1) x ^ (4 : ℕ) = 895 / 351 := by
  rw [giniMean]
  simp [x, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

private lemma gini_x_pq : giniMean 0 2 x ^ (4 : ℕ) = 1849 / 729 := by
  rw [giniMean]
  simp [x, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg]

private lemma le_fourth {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : u ^ (4 : ℕ) ≤ v ^ (4 : ℕ)) : u ≤ v :=
  (pow_le_pow_iff_left₀ hu hv (by norm_num : (4 : ℕ) ≠ 0)).mp h

private lemma nonneg_low_rs : 0 ≤ giniMean 3 (-1) (lowTuple 3 1 3) := by
  rw [giniMean]
  apply Real.rpow_nonneg
  norm_num [lowTuple, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]

private lemma nonneg_low_pq : 0 ≤ giniMean 0 2 (lowTuple 3 1 3) := by
  rw [giniMean]
  apply Real.rpow_nonneg
  norm_num [lowTuple, Fin.sum_univ_three, Real.rpow_intCast, Real.rpow_neg]

private lemma nonneg_high_rs : 0 ≤ giniMean 3 (-1) (highTuple 3 1 3) := by
  rw [giniMean]
  apply Real.rpow_nonneg
  simp [highTuple, Fin.sum_univ_three]
  norm_num

private lemma nonneg_high_pq : 0 ≤ giniMean 0 2 (highTuple 3 1 3) := by
  rw [giniMean]
  apply Real.rpow_nonneg
  simp [highTuple, Fin.sum_univ_three]
  norm_num

private lemma nonneg_x_rs : 0 ≤ giniMean 3 (-1) x := by
  rw [giniMean]
  apply Real.rpow_nonneg
  simp [x, Fin.sum_univ_three]
  norm_num [Real.rpow_intCast, Real.rpow_neg]

theorem result : ¬ claim := by
  intro h
  have hl : giniMean 3 (-1) (lowTuple 3 1 3) ≤ giniMean 0 2 (lowTuple 3 1 3) :=
    le_fourth nonneg_low_rs nonneg_low_pq (by rw [gini_low_rs, gini_low_pq]; norm_num)
  have hh : giniMean 3 (-1) (highTuple 3 1 3) ≤ giniMean 0 2 (highTuple 3 1 3) :=
    le_fourth nonneg_high_rs nonneg_high_pq
      (by rw [gini_high_rs, gini_high_pq]; norm_num)
  have hz := h 3 le_rfl 1 3 (by norm_num) (by norm_num) 3 (-1) 0 2
      (by norm_num) (by norm_num) (by norm_num) hl hh x
      (by intro i; fin_cases i <;> simp [x]; norm_num)
  have hz4 := pow_le_pow_left₀ nonneg_x_rs hz 4
  rw [gini_x_rs, gini_x_pq] at hz4
  norm_num at hz4

end D5.S3.ArithSums.GiniMeanEndpointComparison
