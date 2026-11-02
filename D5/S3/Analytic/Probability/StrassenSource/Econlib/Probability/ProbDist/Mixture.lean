/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.FinDist.Basic
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.Basic

/-!
# Finite mixtures of `ProbDist`

A finite **mixture** of probability laws `ds : Fin n → ProbDist α` with mixing weights
`w : FinDist (Fin n)` is the convex combination `ProbDist.finMixture w ds = ∑ i, w(i) • ds(i)`.

## Main definitions

* `ProbDist.finMixture w ds` — the convex combination `∑ i, w(i) • dᵢ`.

## Main statements

* `ProbDist.expect_finMixture` — the expectation under a mixture is the weighted average of the
  component expectations.

## Tags

probability, mixture, convex combination
-/

@[expose] public section

open MeasureTheory BigOperators

namespace Econlib.Probability

namespace ProbDist

variable {α : Type*} [MeasurableSpace α]

/-- Finite mixture: `∑_i w(i) · dᵢ`. -/
noncomputable def finMixture {n : ℕ} (w : FinDist (Fin n))
    (ds : Fin n → ProbDist α) : ProbDist α :=
  ⟨∑ i, ENNReal.ofReal (w.pmf i) • (ds i).toMeasure, by
    constructor
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul]
    simp only [measure_univ]
    simp only [mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => w.nonneg i)]
    rw [w.sum_one]; simp⟩

/-- The expectation of an integrable `f` under a finite mixture is the weighted average of the
component expectations: `∑ i, w(i) · 𝔼_{dᵢ}[f]`. -/
lemma expect_finMixture {n : ℕ} (w : FinDist (Fin n))
    (ds : Fin n → ProbDist α) (f : α → ℝ)
    (hf : ∀ i, Integrable f (ds i).toMeasure) :
    (finMixture w ds).expect f = ∑ i, w.pmf i * (ds i).expect f := by
  simp only [expect, finMixture]
  change ∫ x, f x ∂(∑ i, ENNReal.ofReal (w.pmf i) • (ds i).toMeasure) =
    ∑ i, w.pmf i * ∫ x, f x ∂(ds i).toMeasure
  rw [integral_finset_sum_measure]
  · congr 1; ext i
    rw [integral_smul_measure, ENNReal.toReal_ofReal (w.nonneg i), smul_eq_mul]
  · intro i _; exact (hf i).smul_measure (ENNReal.ofReal_ne_top)

end ProbDist

end Econlib.Probability
