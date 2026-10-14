/- GID: D5/S3/Quantum/AURICOmega/ExponentialTail
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/ExponentialTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Geometric remainder control for the analytic exponential in a real Banach algebra. -/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open NormedSpace
namespace D5.S3.Quantum.AURICOmega.ExponentialTail

private lemma coefficient_succ (r : ℝ) (m : ℕ) :
    r ^ (m + 1) / ((m + 1).factorial : ℝ) =
      (r / (m + 1)) * (r ^ m / (m.factorial : ℝ)) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private lemma coefficient_bound (r : ℝ) (hr : 0 ≤ r) (n k : ℕ) :
    r ^ (k + n) / ((k + n).factorial : ℝ) ≤
      (r ^ n / (n.factorial : ℝ)) * (r / (n + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + n = (k + n) + 1 by omega, coefficient_succ]
    have hden : (n + 1 : ℝ) ≤ (k + n + 1 : ℕ) := by
      exact_mod_cast (show n + 1 ≤ k + n + 1 by omega)
    have hratio : r / (k + n + 1 : ℕ) ≤ r / (n + 1) :=
      div_le_div_of_nonneg_left hr (by positivity) hden
    simp only [Nat.cast_add, Nat.cast_one] at hratio ⊢
    calc
      _ ≤ (r / (n + 1)) * ((r ^ n / (n.factorial : ℝ)) * (r / (n + 1)) ^ k) :=
        mul_le_mul hratio ih (by positivity) (by positivity)
      _ = (r ^ n / (n.factorial : ℝ)) * (r / (n + 1)) ^ (k + 1) := by
        rw [pow_succ]; ring

/-- A factorial series tail is bounded by its first term times a geometric sum.
The norm is submultiplicative; matrices use the induced row-sum norm. -/
theorem exp_remainder_le {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    [CompleteSpace B] [NormOneClass B] (x : B) (r : ℝ) (n : ℕ)
    (hr : 0 ≤ r) (hx : ‖x‖ ≤ r) (hn : r < n + 1) :
    ‖exp x - ∑ k ∈ Finset.range n, ((k.factorial : ℝ)⁻¹) • x ^ k‖ ≤
      (r ^ n / (n.factorial : ℝ)) / (1 - r / (n + 1)) := by
  let f : ℕ → B := fun k => ((k.factorial : ℝ)⁻¹) • x ^ k
  have hs : HasSum f (exp x) := exp_series_hasSum_exp' x
  have ht : HasSum (fun k => f (k + n))
      (exp x - ∑ k ∈ Finset.range n, f k) := by
    apply (hasSum_nat_add_iff n).2
    simpa only [sub_add_cancel] using hs
  have hratio : r / (n + 1) < 1 := (div_lt_one (by positivity)).2 hn
  have hgeom := (hasSum_geometric_of_lt_one
    (by positivity : 0 ≤ r / (n + 1)) hratio).mul_left (r ^ n / (n.factorial : ℝ))
  have hterm (k : ℕ) : ‖f (k + n)‖ ≤
      (r ^ n / (n.factorial : ℝ)) * (r / (n + 1)) ^ k := by
    calc
      ‖f (k + n)‖ = (1 / ((k + n).factorial : ℝ)) * ‖x ^ (k + n)‖ := by
        simp [f, norm_smul]
      _ ≤ (1 / ((k + n).factorial : ℝ)) * r ^ (k + n) :=
        mul_le_mul_of_nonneg_left
          ((norm_pow_le x _).trans (pow_le_pow_left₀ (norm_nonneg x) hx _)) (by positivity)
      _ = r ^ (k + n) / ((k + n).factorial : ℝ) := by ring
      _ ≤ _ := coefficient_bound r hr n k
  simpa only [div_eq_mul_inv] using ht.norm_le_of_bounded hgeom hterm

end D5.S3.Quantum.AURICOmega.ExponentialTail
