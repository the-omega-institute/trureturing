/- GID: D5/S3/Combinatorics/BinomialBases/MatharA001722
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MatharA001722
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The signed Stirling coefficient sequence A001722 satisfies Mathar's recurrence and is D-finite as an ordinary rational formal power series. -/

/-
The source is OEIS A001722, revision 26, formula field:
https://oeis.org/A001722/internal?fmt=text
The Crstici signed Stirling sum is the definition. Mathar's conjecture asks for
both the displayed recurrence and D-finiteness of its ordinary series.
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
namespace D5.S3.Combinatorics.BinomialBases.MatharA001722
open Polynomial

private noncomputable def falling (N : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range N, (X - C (i : ℤ))

/-- Signed first-kind Stirling numbers, defined by the falling product. -/
noncomputable def s (N K : ℕ) : ℤ := (falling N).coeff K

/-- The full Crstici sum, in signed first-kind convention. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * ((k + 2).choose 2 : ℤ) * (5 : ℤ) ^ k * s (n + 2) (k + 2)

/-- Ordinary formal generating series over the rationals. -/
noncomputable def G : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))

private noncomputable def D : PowerSeries ℚ → PowerSeries ℚ := PowerSeries.derivative

private def Recurrence : Prop := ∀ n : ℕ, 3 ≤ n →
  a n + 3 * (-(n : ℤ) - 5) * a (n - 1) +
    (3 * (n : ℤ)^2 + 27 * (n : ℤ) + 61) * a (n - 2) -
    ((n : ℤ) + 4)^3 * a (n - 3) = 0

private def DFinite : Prop := ∃ (r : ℕ) (p : ℕ → Polynomial ℚ),
  (∃ j : ℕ, j ≤ r ∧ p j ≠ 0) ∧
  (∑ j ∈ Finset.range (r + 1), (p j : PowerSeries ℚ) * (D^[j]) G) = 0

def claim : Prop := Recurrence ∧ DFinite

private noncomputable def shifted (n : ℕ) : Polynomial ℤ :=
  C ((-1 : ℤ)^n) * taylor (-5) (falling (n + 2))

private theorem falling_degree (N : ℕ) : (falling N).natDegree ≤ N := by
  have hp := Polynomial.natDegree_prod_le (R := ℤ) (Finset.range N)
    (fun i : ℕ => (X - C (i : ℤ) : Polynomial ℤ))
  simpa only [falling, natDegree_X_sub_C, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one] using hp


private theorem shifted_coeff (n : ℕ) : (shifted n).coeff 2 = a n := by
  have hd : (hasseDeriv 2 (falling (n+2))).natDegree < n+1 := by
    have h := Polynomial.natDegree_hasseDeriv_le (falling (n+2)) 2
    have h' := falling_degree (n+2)
    omega
  rw [shifted, coeff_C_mul, taylor_coeff, eval_eq_sum_range' hd, Finset.mul_sum, a]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hasseDeriv_coeff]
  simp only [s]
  rw [show (-5 : ℤ) = (-1) * 5 by norm_num, mul_pow, pow_add]
  ring

private theorem shifted_step (n : ℕ) :
    shifted (n+1) = shifted n * (C ((n : ℤ)+7) - X) := by
  have hf : falling ((n+2)+1) = falling (n+2) * (X - C ((n+2 : ℕ) : ℤ)) := by
    simp only [falling, Finset.prod_range_succ]
  have ht : taylor (-5) (X - C ((n+2 : ℕ) : ℤ)) = X - C ((n : ℤ)+7) := by
    rw [taylor_apply, sub_comp, X_comp, C_comp]
    simp only [Nat.cast_add, Nat.cast_ofNat, C_add, C_neg, C_ofNat]
    ring
  unfold shifted
  rw [show n+1+2 = (n+2)+1 by omega, hf, taylor_mul, ht, pow_succ,
    C_mul, C_neg, C_1]
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
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_pow,
      map_ofNat, C_1]
    ring
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff 2) hp
  simpa only [coeff_sub, coeff_add, coeff_C_mul, shifted_coeff, coeff_neg,
    coeff_X_pow_mul', show ¬3 ≤ 2 by omega, ite_false, neg_zero] using hc

private theorem recurrence_rational (m : ℕ) :
    (a (m+3) : ℚ) - 3*((m : ℚ)+8)*(a (m+2) : ℚ) +
      (3*(m : ℚ)^2+45*(m : ℚ)+169)*(a (m+1) : ℚ) -
      ((m : ℚ)+7)^3*(a m : ℚ) = 0 := by
  exact_mod_cast recurrence_forward m

private theorem initial : a 0 = 1 ∧ a 1 = 18 ∧ a 2 = 251 := by
  norm_num [a, s, falling, Finset.sum_range_succ, Finset.prod_range_succ,
    Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one, Nat.choose]

/-- A nonzero fourth-order homogeneous differential operator. -/
private noncomputable def op : ℕ → Polynomial ℚ
  | 0 => -18 + 254 * X - 1029 * X^2
  | 1 => 1 - 24 * X + 253 * X^2 - 1019 * X^3
  | 2 => -3 * X^2 + 54 * X^3 - 289 * X^4
  | 3 => 3 * X^4 - 30 * X^5
  | 4 => -X^6
  | _ => 0

private noncomputable def term (d j : ℕ) : PowerSeries ℚ :=
  PowerSeries.X^d * (D^[j]) G

private theorem term_coeff (d j n : ℕ) :
    PowerSeries.coeff n (term d j) =
    if d ≤ n then ((n-d+1).ascFactorial j : ℚ) * (a (n-d+j) : ℚ) else 0 := by
  rw [term, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp [D, PowerSeries.coeff_iterate_derivative, G]

private theorem op_expansion :
    (∑ j ∈ Finset.range 5, (op j : PowerSeries ℚ) * (D^[j]) G) =
    -18*term 0 0 + 254*term 1 0 - 1029*term 2 0 +
    term 0 1 - 24*term 1 1 + 253*term 2 1 -
    1019*term 3 1 - 3*term 2 2 +
    54*term 3 2 - 289*term 4 2 +
    3*term 4 3 - 30*term 5 3 - term 6 4 := by
  have cn (n : ℕ) [n.AtLeastTwo] :
      ((ofNat(n) : Polynomial ℚ) : PowerSeries ℚ) = (ofNat(n) : PowerSeries ℚ) :=
    map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, op,
    Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_neg, Polynomial.coe_mul,
    Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_X,
    term, pow_zero, pow_one, one_mul, Function.iterate_zero_apply, Function.iterate_one, cn]
  ring

private theorem annihilates :
    (∑ j ∈ Finset.range 5, (op j : PowerSeries ℚ) * (D^[j]) G) = 0 := by
  rw [op_expansion]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, neg_mul, map_neg, PowerSeries.coeff_ofNat_mul,
    map_zero, term_coeff]
  by_cases hn : n < 6
  · have h0 := initial.1
    have h1 := initial.2.1
    have h2 := initial.2.2
    have hr0 := recurrence_rational 0
    have hr1 := recurrence_rational 1
    have hr2 := recurrence_rational 2
    have hr3 := recurrence_rational 3
    interval_cases n <;>
      norm_num [Nat.ascFactorial_succ, h0, h1, h2] at *
    all_goals first | linear_combination 3*hr0 | linear_combination 4*hr1 |
      linear_combination 5*hr2 | linear_combination 6*hr3
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 6 ≤ n by omega)
    rw [show n = m+6 by omega]
    have hr := recurrence_rational (m+4)
    simp (disch := omega) [Nat.add_sub_assoc, Nat.ascFactorial_succ,
      Nat.cast_add, Nat.cast_mul, Nat.add_assoc] at hr ⊢
    linear_combination ((m : ℚ)+7)*hr

/-- Both original clauses of Mathar's conjecture, for the literal signed sum. -/
theorem result : claim := by
  constructor
  · intro n hn
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [show n = m+3 by omega]
    have h := recurrence_forward m
    convert h using 1
    simp [Nat.add_sub_assoc, Nat.cast_add]
    ring
  · refine ⟨4, op, ⟨4, le_rfl, ?_⟩, annihilates⟩
    simp [op]

end D5.S3.Combinatorics.BinomialBases.MatharA001722
