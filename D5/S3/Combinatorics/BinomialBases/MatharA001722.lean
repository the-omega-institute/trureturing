/- GID: D5/S3/Combinatorics/BinomialBases/MatharA001722
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MatharA001722
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The signed Stirling coefficient sequence A001722 satisfies Mathar's recurrence and is D-finite as an ordinary rational formal power series. -/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators
namespace D5.S3.Combinatorics.BinomialBases.MatharA001722
open Polynomial

noncomputable def falling (N : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range N, (X - C (i : ℤ))

/-- Signed first-kind Stirling numbers, defined by the falling product. -/
noncomputable def s (N K : ℕ) : ℤ := (falling N).coeff K

/-- The full Crstici sum, in signed first-kind convention. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * ((k + 2).choose 2 : ℤ) * (5 : ℤ) ^ k * s (n + 2) (k + 2)

/-- Ordinary formal generating series over the rationals. -/
noncomputable def G : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def D : PowerSeries ℚ → PowerSeries ℚ := PowerSeries.derivative

def Recurrence : Prop := ∀ n : ℕ, 3 ≤ n →
  a n + 3 * (-(n : ℤ) - 5) * a (n - 1) +
    (3 * (n : ℤ)^2 + 27 * (n : ℤ) + 61) * a (n - 2) -
    ((n : ℤ) + 4)^3 * a (n - 3) = 0

def DFinite : Prop := ∃ (r : ℕ) (p : ℕ → Polynomial ℚ),
  (∃ j : ℕ, j ≤ r ∧ p j ≠ 0) ∧
  (∑ j ∈ Finset.range (r + 1), (p j : PowerSeries ℚ) * (D^[j]) G) = 0

def claim : Prop := Recurrence ∧ DFinite

private noncomputable def shifted (n : ℕ) : Polynomial ℤ :=
  C ((-1 : ℤ)^n) * taylor (-5) (falling (n + 2))

private theorem falling_degree (N : ℕ) : (falling N).natDegree ≤ N := by
  simpa [falling] using
    (Polynomial.natDegree_prod_le (Finset.range N) (fun i => (X - C (i : ℤ))))

private theorem shifted_coeff (n : ℕ) : (shifted n).coeff 2 = a n := by
  have hd : (hasseDeriv 2 (falling (n+2))).natDegree < n+1 := by
    have h := Polynomial.natDegree_hasseDeriv_le (falling (n+2)) 2
    have h' := falling_degree (n+2)
    omega
  rw [shifted, coeff_C_mul, taylor_coeff, eval_eq_sum_range' hd, Finset.mul_sum, a]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hasseDeriv_coeff]
  simp only [a, s] at *
  rw [show (-5 : ℤ) = (-1) * 5 by norm_num, mul_pow, pow_add]
  ring

private theorem shifted_step (n : ℕ) :
    shifted (n+1) = shifted n * (C ((n : ℤ)+7) - X) := by
  simp only [shifted, falling, show n+1+2 = (n+2)+1 by omega,
    Finset.prod_range_succ, taylor_mul, map_sub, taylor_X, taylor_C,
    pow_succ, Nat.cast_add, Nat.cast_ofNat]
  simp only [← C_mul]
  ring

private theorem recurrence_forward (m : ℕ) :
    a (m+3) - 3*((m : ℤ)+8)*a (m+2) +
      (3*(m : ℤ)^2+45*(m : ℤ)+169)*a (m+1) -
      ((m : ℤ)+7)^3*a m = 0 := by
  have hp : shifted (m+3) - C (3*((m : ℤ)+8))*shifted (m+2) +
      C (3*(m : ℤ)^2+45*(m : ℤ)+169)*shifted (m+1) -
      C (((m : ℤ)+7)^3)*shifted m = - (X^3 * shifted m) := by
    rw [show m+3 = (m+2)+1 by omega, shifted_step,
      show m+2 = (m+1)+1 by omega, shifted_step, shifted_step]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_mul, map_pow,
      map_ofNat]
    ring
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff 2) hp
  simpa only [coeff_sub, coeff_add, coeff_C_mul, shifted_coeff, coeff_neg,
    coeff_mul_X_pow', show ¬3 ≤ 2 by omega, if_false, neg_zero] using hc

end D5.S3.Combinatorics.BinomialBases.MatharA001722
