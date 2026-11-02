/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.FinDist.Basic
public import Mathlib.Data.Real.StarOrdered

/-!
# Expectations for finite distributions

This file defines expectation and variance for `FinDist` and proves basic algebraic rules.

## Main definitions

* `FinDist.expect`: Expectation as a finite sum.
* `FinDist.variance`: Variance of a real-valued function.

## Main statements

* `FinDist.expect_add`: Additivity of expectation.
* `FinDist.expect_mixture`: Expectation of a finite mixture.
* `FinDist.variance_nonneg`: Nonnegativity of variance.

## Tags

probability, finite distributions, expectation, variance
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Expected value for a finite distribution. -/
noncomputable def expect (d : FinDist α) (f : α → ℝ) : ℝ :=
  ∑ a, d.pmf a * f a

/-- Variance for a finite distribution. -/
noncomputable def variance (d : FinDist α) (f : α → ℝ) : ℝ :=
  d.expect (fun a => (f a)^2) - (d.expect f)^2

@[findist_eval] lemma expect_eq_sum (d : FinDist α) (f : α → ℝ) :
    d.expect f = ∑ a, d.pmf a * f a := rfl

/-- The expectation of a constant is that constant. -/
lemma expect_const (d : FinDist α) (c : ℝ) : d.expect (fun _ => c) = c := by
  dsimp [expect]
  rw [← Finset.sum_mul, d.sum_one, one_mul]

/-- Expectation is additive. -/
lemma expect_add (d : FinDist α) (f g : α → ℝ) : d.expect (f + g) = d.expect f + d.expect g := by
  dsimp [expect]
  simp_rw [mul_add, Finset.sum_add_distrib]

/-- Expectation is homogeneous in scalar multiplication. -/
lemma expect_smul (d : FinDist α) (c : ℝ) (f : α → ℝ) : d.expect (c • f) = c * d.expect f := by
  dsimp [expect]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The expectation of a nonnegative function is nonnegative. -/
lemma expect_nonneg (d : FinDist α) (f : α → ℝ) (h : ∀ a, 0 ≤ f a) :
    0 ≤ d.expect f := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (d.nonneg a) (h a)

/-- Expectation is monotone in the integrand. -/
lemma expect_mono (d : FinDist α) (f g : α → ℝ) (h : ∀ a, f a ≤ g a) :
    d.expect f ≤ d.expect g := by
  dsimp [expect]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (h a) (d.nonneg a)

@[findist_eval] lemma expect_pure (a : α) (f : α → ℝ) : (FinDist.pure a).expect f = f a := by
  simp [expect, pure]

/-- A distribution with full mass at `a` has expectation `f a`, with the point-mass fact supplied
as a `pmf` equation rather than structurally. -/
lemma expect_of_pmf_eq_one {d : FinDist α} {a : α} (h : d.pmf a = 1) (f : α → ℝ) :
    d.expect f = f a := by
  rw [eq_pure_of_pmf_eq_one h, expect_pure]

/-- A distribution supported on maximizers cannot be beaten: If every on-support outcome of `d`
maximizes `f`, then `d` weakly dominates every distribution in `f`-expectation. -/
lemma expect_le_expect_of_support_max {d : FinDist α} {f : α → ℝ}
    (h : ∀ a, 0 < d.pmf a → ∀ b, f b ≤ f a) (d' : FinDist α) :
    d'.expect f ≤ d.expect f := by
  -- Any on-support outcome `a₀` of `d` bounds `f` everywhere.
  obtain ⟨a₀, ha₀⟩ := d.exists_pmf_pos
  have hmax : ∀ b, f b ≤ f a₀ := h a₀ ha₀
  -- `d'` is dominated by the constant bound `f a₀`.
  have h_le : d'.expect f ≤ f a₀ :=
    le_of_le_of_eq (expect_mono d' f (fun _ => f a₀) hmax) (expect_const d' (f a₀))
  -- `d` concentrates on maximizers, where `f` is constantly `f a₀` by mutual domination.
  have h_eq : d.expect f = f a₀ := by
    rw [expect_eq_sum]
    have hterm : ∀ a ∈ Finset.univ, d.pmf a * f a = d.pmf a * f a₀ := by
      intro a _
      rcases eq_or_lt_of_le (d.nonneg a) with hz | hp
      · rw [← hz]; ring
      · rw [le_antisymm (hmax a) (h a hp a₀)]
    calc ∑ a, d.pmf a * f a = ∑ a, d.pmf a * f a₀ := Finset.sum_congr rfl hterm
    _ = (∑ a, d.pmf a) * f a₀ := by rw [Finset.sum_mul]
    _ = f a₀ := by rw [d.sum_one, one_mul]
  linarith

/-- Converse of `expect_le_expect_of_support_max`: If `d.expect f` is an upper bound for `f`, then
every on-support outcome of `d` attains it. A mixture's expectation can equal the maximum payoff
only if every action the mixture actually plays is itself a maximizer. -/
lemma eq_expect_of_pmf_pos {d : FinDist α} {f : α → ℝ}
    (h : ∀ b, f b ≤ d.expect f) {a : α} (ha : 0 < d.pmf a) :
    f a = d.expect f := by
  -- The weighted shortfall `∑ b, d.pmf b * (d.expect f - f b)` is a sum of nonnegative terms that
  -- telescopes to zero, so every on-support term vanishes.
  have hnonneg : ∀ b ∈ Finset.univ, 0 ≤ d.pmf b * (d.expect f - f b) :=
    fun b _ => mul_nonneg (d.nonneg b) (by linarith [h b])
  have hsum : ∑ b, d.pmf b * (d.expect f - f b) = 0 := by
    have hsplit : ∑ b, d.pmf b * (d.expect f - f b) =
        (∑ b, d.pmf b) * d.expect f - ∑ b, d.pmf b * f b := by
      simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hsplit, d.sum_one, one_mul, ← expect_eq_sum, sub_self]
  have hterm : d.pmf a * (d.expect f - f a) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum a (Finset.mem_univ a)
  -- `d.pmf a > 0` forces the shortfall at `a` to be zero.
  have : d.expect f - f a = 0 := by
    rcases mul_eq_zero.mp hterm with hz | hz
    · exact absurd hz ha.ne'
    · exact hz
  linarith

/-- Expectation of a binary mixture is the convex combination of the two expectations. -/
lemma expect_mixture (t : unitInterval) (d₁ d₂ : FinDist α) (f : α → ℝ) :
    (FinDist.mixture t d₁ d₂).expect f = (t : ℝ) * d₁.expect f + (1 - (t : ℝ)) * d₂.expect f := by
  simp only [expect, mixture]
  have : ∀ a, ((t : ℝ) * d₁.pmf a + (1 - (t : ℝ)) * d₂.pmf a) * f a =
    (t : ℝ) * (d₁.pmf a * f a) + (1 - (t : ℝ)) * (d₂.pmf a * f a) := fun a => by ring
  simp_rw [this, Finset.sum_add_distrib, ← (Finset.mul_sum _ _ _)]

/-- Variance is nonnegative. -/
lemma variance_nonneg (d : FinDist α) (f : α → ℝ) : 0 ≤ d.variance f := by
  unfold variance expect
  set μ := ∑ a, d.pmf a * f a with hμ
  have h1 : 0 ≤ ∑ a, d.pmf a * (f a - μ)^2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (d.nonneg a) (sq_nonneg _))
  have h2 : ∑ a, d.pmf a * (f a - μ)^2 =
    (∑ a, d.pmf a * (f a)^2) - μ^2 := by
    have ha : ∀ a, d.pmf a * (f a - μ)^2 =
      d.pmf a * (f a)^2 - 2 * μ * (d.pmf a * f a) + μ^2 * d.pmf a := fun a => by ring
    simp_rw [ha]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← (Finset.mul_sum _ _ _)]
    rw [show ∑ x : α, μ ^ 2 * d.pmf x = μ ^ 2 * ∑ x, d.pmf x from
      (Finset.mul_sum _ _ _).symm]
    rw [hμ, d.sum_one]; ring
  linarith

end FinDist
end Econlib.Probability
