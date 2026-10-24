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
  rational bounds on each ratio from the bounds on exp 1 finish by linear arithmetic.
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
  have b4 : (e - 8 / 3) / (e - 65 / 24) < 5188239 / 1000000 := by
    rw [div_lt_iff₀ h4]; linarith only [heLo]
  have b3 : (4229025 / 1000000 : ℝ) < (e - 5 / 2) / (e - 8 / 3) := by
    rw [lt_div_iff₀ h3]; linarith only [heHi]
  have b2 : (e - 2) / (e - 5 / 2) < 3290617 / 1000000 := by
    rw [div_lt_iff₀ h2]; linarith only [heLo]
  have b1 : (2392211 / 1000000 : ℝ) < (e - 1) / (e - 2) := by
    rw [lt_div_iff₀ h1]; linarith only [heHi]
  have b3' : (e - 5 / 2) / (e - 8 / 3) * 3 = 3 * (e - 5 / 2) / (e - 8 / 3) := by ring
  have b2' : (e - 2) / (e - 5 / 2) * 3 = 3 * (e - 2) / (e - 5 / 2) := by ring
  linarith only [b4, b3, b2, b1, b3', b2']

/-- Sitnik's universal forward-difference nonnegativity assertion is false. -/
theorem result : ¬ claim := by
  intro h
  have hnonneg := h 3 1 (by norm_num) (by norm_num) 1 (by norm_num)
  exact (not_lt_of_ge hnonneg) witness_neg

end D5.S3.Analytic.ExpRemainderDifferences
