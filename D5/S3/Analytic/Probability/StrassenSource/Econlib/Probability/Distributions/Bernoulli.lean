/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.FinDist.CDF
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.FinDist.Expect

/-!
# Bernoulli distribution

This file defines the Bernoulli distribution as a finite distribution on `Fin 2`, where index `1`
represents success and index `0` represents failure, with success probability `p ∈ [0, 1]`.

## Main definitions

* `FinDist.bernoulli`: Bernoulli distribution with success probability `p`.

## Main statements

* `FinDist.bernoulli_apply_one`: The probability mass at the success outcome equals `p`.
* `FinDist.bernoulli_apply_zero`: The probability mass at the failure outcome equals `1 - p`.
* `FinDist.bernoulli_expect_eq`: Expectation of an arbitrary function under the Bernoulli
  distribution.
* `FinDist.bernoulli_expect`: Expectation of the natural coercion `Fin 2 → ℝ` equals `p`.
* `FinDist.bernoulli_variance`: Variance of the natural coercion equals `p * (1 - p)`.
* `FinDist.bernoulli_cdf_zero`, `FinDist.bernoulli_cdf_one`: The CDF equals `1 - p` at the failure
  outcome and `1` at the success outcome.
* `FinDist.bernoulli_isMode_zero`, `FinDist.bernoulli_isMode_one`: The mode is the failure outcome
  when `p ≤ 1/2` and the success outcome when `1/2 ≤ p`.
* `FinDist.bernoulli_support_univ`: When `0 < p < 1`, the support is all of `Fin 2`.

## Tags

probability, discrete distributions, bernoulli
-/

@[expose] public section

namespace Econlib.Probability

/-- The Bernoulli distribution on `Fin 2` with success probability `p ∈ [0, 1]`, where outcome `1`
occurs with probability `p` and outcome `0` occurs with probability `1 - p`. -/
def FinDist.bernoulli (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FinDist (Fin 2) where
  pmf i := if i.val = 1 then p else 1 - p
  nonneg i := by split <;> linarith
  sum_one := by simp [Fin.sum_univ_two]

/-- The probability mass at the success outcome `⟨1, _⟩` equals `p`. -/
lemma FinDist.bernoulli_apply_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.bernoulli p hp hp1).pmf ⟨1, by decide⟩ = p := by
  simp [bernoulli]

/-- The probability mass at the failure outcome `⟨0, _⟩` equals `1 - p`. -/
lemma FinDist.bernoulli_apply_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.bernoulli p hp hp1).pmf ⟨0, by decide⟩ = 1 - p := by
  simp [bernoulli]

/-- The expectation of `f` under the Bernoulli distribution equals
`(1 - p) * f ⟨0, _⟩ + p * f ⟨1, _⟩`. -/
lemma FinDist.bernoulli_expect_eq (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : Fin 2 → ℝ) :
    (FinDist.bernoulli p hp hp1).expect f =
      (1 - p) * f ⟨0, by decide⟩ + p * f ⟨1, by decide⟩ := by
  simp [FinDist.expect, bernoulli, Fin.sum_univ_two]

/-- The expectation of the natural coercion `Fin 2 → ℝ` under the Bernoulli distribution equals the
success probability `p`. -/
lemma FinDist.bernoulli_expect (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.bernoulli p hp hp1).expect (fun i => (i : ℝ)) = p := by
  rw [FinDist.bernoulli_expect_eq p hp hp1]
  norm_num

/-- The variance of the natural coercion `Fin 2 → ℝ` under the Bernoulli distribution equals
`p * (1 - p)`. -/
lemma FinDist.bernoulli_variance (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.bernoulli p hp hp1).variance (fun i => (i : ℝ)) = p * (1 - p) := by
  simp only [FinDist.variance]
  rw [FinDist.bernoulli_expect_eq p hp hp1, FinDist.bernoulli_expect_eq p hp hp1]
  norm_num
  ring

/-- The CDF at the failure outcome `⟨0, _⟩` equals `1 - p`. -/
@[simp] lemma FinDist.bernoulli_cdf_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.bernoulli p hp hp1).cdf ⟨0, by decide⟩ = 1 - p := by
  rw [FinDist.cdf_eq_sum_ite]
  simp [bernoulli]

/-- The CDF at the success outcome `⟨1, _⟩` equals `1`. -/
@[simp] lemma FinDist.bernoulli_cdf_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.bernoulli p hp hp1).cdf ⟨1, by decide⟩ = 1 := by
  rw [FinDist.cdf_eq_sum_ite]
  simp [Fin.sum_univ_two, bernoulli]

/-- When `p ≤ 1/2`, the failure outcome `⟨0, _⟩` is a mode of the Bernoulli distribution. -/
lemma FinDist.bernoulli_isMode_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : p ≤ 1 / 2) :
    (FinDist.bernoulli p hp hp1).IsMode ⟨0, by decide⟩ := by
  intro i
  fin_cases i
  · exact le_refl _
  · simp only [bernoulli]
    norm_num
    linarith

/-- When `1/2 ≤ p`, the success outcome `⟨1, _⟩` is a mode of the Bernoulli distribution. -/
lemma FinDist.bernoulli_isMode_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : 1 / 2 ≤ p) :
    (FinDist.bernoulli p hp hp1).IsMode ⟨1, by decide⟩ := by
  intro i
  fin_cases i
  · simp only [bernoulli]
    norm_num
    linarith
  · exact le_refl _

/-- When `0 < p < 1`, the support of the Bernoulli distribution is all of `Fin 2`. -/
lemma FinDist.bernoulli_support_univ (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (FinDist.bernoulli p (le_of_lt hp) (le_of_lt hp1)).support = Finset.univ := by
  ext i
  unfold FinDist.support
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases i <;> simp [bernoulli, hp, hp1, sub_pos]

end Econlib.Probability
