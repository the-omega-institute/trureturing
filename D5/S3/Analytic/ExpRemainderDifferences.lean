/- GID: D5/S3/Analytic/ExpRemainderDifferences
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRemainderDifferences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff, mathlib/module/Mathlib.Analysis.Complex.ExponentialBounds]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/ExpRemainderDifferences.claim; result=D5/S3/Analytic/ExpRemainderDifferences.result; claim=D5/S3/Analytic/ExpRemainderDifferences.claim
   digest: A negative third forward difference refutes exponential remainder ratio positivity. -/

/-
admission_basis: open-problem-resolution (#20958; Refuted)
escape_witness: none; the settling proof is bind-only.
Direct frozen dependencies: none (only Mathlib is imported).

Per-declaration judgement form:
* R: proof_shape: bind-only (source definition); consumers: g, witness_neg.
* g: proof_shape: bind-only (source definition); consumers: claim, witness_neg.
* claim: proof_shape: bind-only (source assertion); consumer: result.
* witness_neg: proof_shape: bind-only; consumer: result; escape_witness: none.
  The binomial expansion is supplied by fwdDiff_iter_eq_sum_shift; finite sums,
  denominator clearing and the rational bounds on exp 1 finish by normalization.
* result: proof_shape: bind-only; settling result; escape_witness: none.
  Universal nonnegativity contradicts witness_neg at k = 3, n = 1, x = 1.
-/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.ExpRemainderDifferences

/-- The remainder after the degree n Taylor polynomial of the exponential. -/
def R (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ)

/-- The consecutive remainder ratio, used at natural indices n at least one. -/
def g (n : ℕ) (x : ℝ) : ℝ := R (n - 1) x / R n x

/-- Nonnegativity of every positive-order forward difference at positive arguments. -/
def claim : Prop :=
  ∀ k n : ℕ, 1 ≤ k → 1 ≤ n → ∀ x : ℝ, 0 < x →
    0 ≤ (fwdDiff 1)^[k] (fun m => g m x) n

private theorem witness_neg : (fwdDiff 1)^[3] (fun m => g m 1) 1 < 0 := by
  let e : ℝ := Real.exp 1
  have heLo : (2.7182818283 : ℝ) < e := Real.exp_one_gt_d9
  have heHi : e < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hepos : 0 < e := by linarith only [heLo]
  have h1 : 0 < e - 2 := by linarith only [heLo]
  have h2 : 0 < e - 5 / 2 := by linarith only [heLo]
  have h3 : 0 < e - 8 / 3 := by linarith only [heLo]
  have h4 : 0 < e - 65 / 24 := by linarith only [heLo]
  have hsquare : e ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hepos.le heHi.le 2
  have hcube : e ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hepos.le heHi.le 3
  have hpoly : 12 * e ^ 3 + 34 * e ^ 2 - 457 * e + 750 < 0 := by
    linarith only [heLo, hsquare, hcube]
  have hr0 : R 0 1 = e - 1 := by
    norm_num [R, Finset.sum_range_succ, Nat.factorial, e]
  have hr1 : R 1 1 = e - 2 := by
    norm_num [R, Finset.sum_range_succ, Nat.factorial, e]
  have hr2 : R 2 1 = e - 5 / 2 := by
    norm_num [R, Finset.sum_range_succ, Nat.factorial, e]
  have hr3 : R 3 1 = e - 8 / 3 := by
    norm_num [R, Finset.sum_range_succ, Nat.factorial, e]
  have hr4 : R 4 1 = e - 65 / 24 := by
    norm_num [R, Finset.sum_range_succ, Nat.factorial, e]
  have hdiff : (fwdDiff 1)^[3] (fun m => g m 1) 1 =
      g 4 1 - 3 * g 3 1 + 3 * g 2 1 - g 1 1 := by
    rw [fwdDiff_iter_eq_sum_shift]
    norm_num [Finset.sum_range_succ, zsmul_eq_mul, Nat.choose]
    <;> ring
  rw [hdiff]
  have hg : g 4 1 - 3 * g 3 1 + 3 * g 2 1 - g 1 1 =
      (e - 8 / 3) / (e - 65 / 24) - 3 * (e - 5 / 2) / (e - 8 / 3) +
        3 * (e - 2) / (e - 5 / 2) - (e - 1) / (e - 2) := by
    norm_num only [g, Nat.reduceSub, hr0, hr1, hr2, hr3, hr4]
    <;> ring
  rw [hg]
  have hid :
      (e - 8 / 3) / (e - 65 / 24) - 3 * (e - 5 / 2) / (e - 8 / 3) +
          3 * (e - 2) / (e - 5 / 2) - (e - 1) / (e - 2) =
        (12 * e ^ 3 + 34 * e ^ 2 - 457 * e + 750) /
          (288 * (e - 2) * (e - 5 / 2) * (e - 8 / 3) * (e - 65 / 24)) := by
    have k1 : -2 + e ≠ 0 := by linarith only [heLo]
    have k2 : -5 + e * 2 ≠ 0 := by linarith only [heLo]
    have k3 : -8 + e * 3 ≠ 0 := by linarith only [heLo]
    have k4 : -65 + e * 24 ≠ 0 := by linarith only [heLo]
    rw [eq_div_iff (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) h1) h2) h3) h4).ne']
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3, ne_of_gt h4, k1, k2, k3, k4]
    ring
  rw [hid]
  exact div_neg_of_neg_of_pos hpoly
    (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) h1) h2) h3) h4)

/-- Sitnik's universal forward-difference nonnegativity assertion is false. -/
theorem result : ¬ claim := by
  intro h
  have hnonneg := h 3 1 (by norm_num) (by norm_num) 1 (by norm_num)
  exact (not_lt_of_ge hnonneg) witness_neg

end D5.S3.Analytic.ExpRemainderDifferences
