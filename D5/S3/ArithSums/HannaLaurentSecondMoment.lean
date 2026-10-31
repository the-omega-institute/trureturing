/- GID: D5/S3/ArithSums/HannaLaurentSecondMoment
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaLaurentSecondMoment
   mirror-E: none(waiver:symbolic-laurent-coefficient-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: none
   digest: The full signed bilateral Laurent second moment in A391810 formula (4). -/

import D5.S3.ArithSums.HannaLaurentRowSums
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Polynomial

namespace D5.S3.ArithSums.HannaLaurentSecondMoment

open D5.S3.ArithSums.HannaLaurentRowSums

noncomputable section

private def eulerSq (p : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.X * Polynomial.derivative (Polynomial.X * Polynomial.derivative p)

private theorem eulerSq_coeff (p : Polynomial ℤ) (m : ℕ) :
    (eulerSq p).coeff m = (m : ℤ)^2 * p.coeff m := by
  cases m with
  | zero => simp [eulerSq]
  | succ m =>
    simp only [eulerSq, Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

private theorem eulerSq_natDegree_le (p : Polynomial ℤ) :
    (eulerSq p).natDegree ≤ p.natDegree := by
  by_cases hp0 : p.natDegree = 0
  · have hder : Polynomial.derivative p = 0 := Polynomial.derivative_of_natDegree_zero hp0
    simp [eulerSq, hder]
  · have hp_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hp0
    unfold eulerSq
    calc
      (Polynomial.X * Polynomial.derivative (Polynomial.X * Polynomial.derivative p)).natDegree ≤
          Polynomial.X.natDegree + (Polynomial.derivative (Polynomial.X * Polynomial.derivative p)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + ((Polynomial.X * Polynomial.derivative p).natDegree - 1) := by
        simp only [Polynomial.natDegree_X]
        exact Nat.add_le_add_left (Polynomial.natDegree_derivative_le _) 1
      _ ≤ p.natDegree := by
        have h' : (Polynomial.X * Polynomial.derivative p).natDegree ≤ p.natDegree := by
          calc
            (Polynomial.X * Polynomial.derivative p).natDegree ≤
                Polynomial.X.natDegree + (Polynomial.derivative p).natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ p.natDegree := by
              simp only [Polynomial.natDegree_X]
              have h := Polynomial.natDegree_derivative_le p
              omega
        omega

private theorem weighted_coeff_eq_eulerSq_eval (p : Polynomial ℤ) (B : ℕ)
    (hp : p.natDegree ≤ B) :
    (∑ m ∈ Finset.range (B + 1), (m : ℤ)^2 * p.coeff m) =
      (eulerSq p).eval 1 := by
  have hq : (eulerSq p).natDegree < B + 1 := by
    exact lt_of_le_of_lt (eulerSq_natDegree_le p) (Nat.lt_succ_iff.mpr hp)
  rw [Polynomial.eval_eq_sum_range' hq]
  simp only [one_pow, mul_one]
  rw [Finset.sum_congr rfl]
  intro m hm
  rw [eulerSq_coeff]

private theorem term_eulerSq_eval (q m : ℕ) :
    (eulerSq (Polynomial.X ^ q * (1 - Polynomial.X ^ q) ^ m)).eval 1 =
      if m = 0 then (q : ℤ)^2 else if m = 1 then -3 * (q : ℤ)^2
      else if m = 2 then 2 * (q : ℤ)^2 else 0 := by
  by_cases hm0 : m = 0
  · subst m
    by_cases hq0 : q = 0
    · subst q
      simp [eulerSq, Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X_pow]
    · have hqpos : 1 ≤ q := by omega
      simp [eulerSq, Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X_pow]
      push_cast
      rw [Nat.cast_sub hqpos]
      ring
  by_cases hm1 : m = 1
  · subst m
    by_cases hq0 : q = 0
    · subst q
      simp [eulerSq, Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X_pow]
    · have hqpos : 1 ≤ q := by omega
      simp [eulerSq, Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X_pow]
      push_cast
      rw [Nat.cast_sub hqpos]
      ring
  by_cases hm2 : m = 2
  · subst m
    simp [eulerSq, Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.derivative_X_pow]
    push_cast
    ring
  have hm1pos : 0 < m - 1 := by omega
  have hm2pos : 0 < m - 1 - 1 := by omega
  simp [eulerSq, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X_pow, hm0, hm1, hm2, zero_pow hm1pos.ne', zero_pow hm2pos.ne']

private theorem eulerSq_add (p r : Polynomial ℤ) :
    eulerSq (p + r) = eulerSq p + eulerSq r := by
  simp [eulerSq, Polynomial.derivative_add, Polynomial.derivative_mul,
    add_mul, mul_add, add_assoc, add_left_comm, add_comm]

private theorem eulerSq_sum (s : Finset ℕ) (f : ℕ → Polynomial ℤ) :
    eulerSq (∑ j ∈ s, f j) = ∑ j ∈ s, eulerSq (f j) := by
  induction s using Finset.induction_on with
  | empty => simp [eulerSq]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [eulerSq_add, ih]

private theorem row_eulerSq_eval (n : ℕ) (hn : 2 ≤ n) :
    (eulerSq (rowPolynomial n)).eval 1 = -(2 * (n : ℤ) - 5) := by
  rw [show rowPolynomial n = -1 + ∑ j ∈ Finset.range n,
      Polynomial.X ^ (j + 1) * (1 - Polynomial.X ^ (j + 1)) ^ (n - (j + 1)) by rfl]
  rw [eulerSq_add, eulerSq_sum]
  have hneg : (eulerSq (-1 : Polynomial ℤ)).eval 1 = 0 := by simp [eulerSq]
  rw [Polynomial.eval_add, hneg, zero_add]
  rw [Polynomial.eval_finsetSum]
  simp_rw [term_eulerSq_eval]
  by_cases hn2 : n = 2
  · subst n
    norm_num [Finset.sum_range_succ]
  · have hn3 : 3 ≤ n := by omega
    have hprefix : ∀ j ∈ Finset.range (n - 3),
        (if n - (j + 1) = 0 then ((j + 1 : ℕ) : ℤ)^2
         else if n - (j + 1) = 1 then -3 * ((j + 1 : ℕ) : ℤ)^2
         else if n - (j + 1) = 2 then 2 * ((j + 1 : ℕ) : ℤ)^2 else 0) = 0 := by
      intro j hj
      have hjlt : j < n - 3 := Finset.mem_range.mp hj
      have h0 : n - (j + 1) ≠ 0 := by omega
      have h1 : n - (j + 1) ≠ 1 := by omega
      have h2 : n - (j + 1) ≠ 2 := by omega
      simp [h0, h1, h2]
    have hdecomp : n = (n - 3) + 3 := by omega
    rw [show Finset.range n = Finset.range ((n - 3) + 3) from congrArg Finset.range hdecomp]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero hprefix]
    have h0 : n - (n - 3 + 1) = 2 := by omega
    have h1 : n - (n - 3 + 1 + 1) = 1 := by omega
    have h2 : n - (n - 3 + 2 + 1) = 0 := by omega
    simp [h0, h1, h2, Nat.cast_sub hn3] <;> ring


/-- The signed second moment of every full integer row. -/
private theorem integer_second_moment_exact (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (((n + 1) / 2)^2 + 1),
      (k : ℤ)^2 * rowEntry n k) = -(2 * (n : ℤ) - 5) := by
  change (∑ k ∈ Finset.range (rowBound n + 1),
    (k : ℤ)^2 * (rowPolynomial n).coeff k) = _
  rw [weighted_coeff_eq_eulerSq_eval _ _ (row_degree n), row_eulerSq_eval n hn]

/-- The literal formal Laurent coefficient moment; no evaluation of the series. -/
theorem result (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (((n + 1) / 2)^2 + 1),
      (k : ℚ)^2 * (series n (by omega)).coeff (-(k : ℤ))) =
      (-(2 * (n : ℤ) - 5) : ℤ) := by
  simp_rw [series_coefficient]
  exact_mod_cast integer_second_moment_exact n hn

end
end D5.S3.ArithSums.HannaLaurentSecondMoment
