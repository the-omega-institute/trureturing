/- GID: D5/S3/Analytic/LogFunctionMonotoneChain
   generality: I
   mirror-B: D5/B/S3/Analytic/LogFunctionMonotoneChain
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed derivative regions of polynomial log-functions form a descending chain. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact

/-! Derivative-sign nesting for polynomial log-functions on the positive half-line. -/

namespace D5.S3.Analytic.LogFunctionMonotoneChain

open Polynomial Set Filter
open scoped Topology

/-- The source's univariate log-function, restricted in all sign conditions to `x > 0`. -/
noncomputable def logFunction (p : Polynomial ℝ) (x : ℝ) : ℝ := p.eval (Real.log x) / x

/-- The degree-bounded region where the signed derivative of order `k` is nonnegative. -/
def derivativeRegion (n k : ℕ) : Set (Polynomial ℝ) :=
  {p | p.natDegree ≤ n ∧ ∀ x : ℝ, 0 < x →
    0 ≤ (-1 : ℝ) ^ k * iteratedDeriv k (logFunction p) x}

/-- Complete monotonicity on the positive half-line, including the zeroth derivative. -/
def completelyMonotone (f : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ k * iteratedDeriv k f x

/-- Nesting and the intersection description hold for every degree bound, including zero. -/
def claim : Prop :=
  ∀ n : ℕ, (∀ k : ℕ, 1 ≤ k → derivativeRegion n (k + 1) ⊆ derivativeRegion n k) ∧
    ∀ p : Polynomial ℝ, p.natDegree ≤ n →
      ((∀ k : ℕ, 1 ≤ k → p ∈ derivativeRegion n k) ↔ completelyMonotone (logFunction p))

private noncomputable def derivativePolynomial (p : Polynomial ℝ) (j : ℕ) : Polynomial ℝ :=
  Nat.rec p (fun j q => (j + 1 : ℝ) • q - q.derivative) j

private lemma signed_derivative_formula (p : Polynomial ℝ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ j * iteratedDeriv j (logFunction p) x =
      x⁻¹ ^ (j + 1) * (derivativePolynomial p j).eval (Real.log x) := by
  sorry

private lemma sign_transfer (p : Polynomial ℝ) (n j : ℕ) :
    p ∈ derivativeRegion n j ↔
      p.natDegree ≤ n ∧ ∀ y : ℝ, 0 ≤ (derivativePolynomial p j).eval y := by
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun y => ?_⟩
    have hy := h (Real.exp y) (Real.exp_pos y)
    rw [signed_derivative_formula p j (Real.exp_pos y), Real.log_exp] at hy
    exact nonneg_of_mul_nonneg_right hy (by positivity)
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun x hx => ?_⟩
    rw [signed_derivative_formula p j hx]
    exact mul_nonneg (by positivity) (h _)

private lemma nonneg_of_sub_derivative (q : Polynomial ℝ) {a : ℝ} (ha : 0 < a)
    (h : ∀ y : ℝ, 0 ≤ (a • q - q.derivative).eval y) : ∀ y : ℝ, 0 ≤ q.eval y := by
  sorry

private lemma descending (n k : ℕ) : derivativeRegion n (k + 1) ⊆ derivativeRegion n k := by
  intro p hp
  rw [sign_transfer] at hp ⊢
  refine ⟨hp.1, nonneg_of_sub_derivative (derivativePolynomial p k)
    (a := k + 1) (by positivity) ?_⟩
  simpa only [derivativePolynomial, Nat.rec_add_one] using hp.2

private lemma intersection (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ n) :
    (∀ k : ℕ, 1 ≤ k → p ∈ derivativeRegion n k) ↔ completelyMonotone (logFunction p) := by
  constructor
  · intro h k
    cases k with
    | zero => exact (descending n 0 (h 1 le_rfl)).2
    | succ k => exact (h (k + 1) (by omega)).2
  · intro h k _
    exact ⟨hp, h k⟩

theorem result : claim := by
  intro n
  exact ⟨fun k _ => descending n k, intersection n⟩

end D5.S3.Analytic.LogFunctionMonotoneChain
