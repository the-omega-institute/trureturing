/- GID: D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kurkov's shifted array equals every positive convolution-row polynomial. -/

/-
result:
  proof_shape: content; the induction in kurkov_coeff remains after helper inlining.
  escape_witness: kurkov_coeff, the shifted-tail coefficient invariant.
  admission_basis: open-problem-resolution (#24109; Proved).
Direct frozen dependencies for result, source_eq, tail_split,
source_pow_coeff_succ, source_pow_coeff_zero and kurkov_coeff:
  GID: D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.tail
  statement_id: sha256:866d2544f66c1d06437a72737a30260611f3d3ad3546581a69fd50db1c634bb4
Direct frozen dependencies for row_as_of_fn, row_coeff and the source definitions: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25374.

Private theorem classifications and consumers:
  source_eq: bind-only; source_pow_coeff_succ and source_pow_coeff_zero.
  tail_split: bind-only; kurkov_coeff.
  source_pow_coeff_succ: bind-only; kurkov_coeff and result.
  source_pow_coeff_zero: bind-only; result.
  kurkov_coeff: content; result.
  row_as_of_fn: bind-only; row_coeff.
  row_coeff: bind-only; result.
The coefficient identities
use pinned Mathlib owners, including eq_X_mul_shift_add_const,
coeff_succ_X_mul, coeff_X_pow_mul', ofFn_eq_sum_monomial,
ofFn_coeff_eq_val_of_lt, and ofFn_coeff_eq_zero_of_ge.

The definitions preserve the source's coefficient formula and positive-column
recursion. The zero row and zero column are totalized by zero; a 0 is unused.
The source's product order agrees by commutativity with X * C (a k) * R(n,1).
The tail is the existing RecursiveBoundaryRowSeries.tail. Its elaborated
type has no ring-instance parameter and applies to every coefficient type.
The row polynomial retains the source's finite-sum expression; row_as_of_fn
identifies it with Polynomial.ofFn for coefficient extraction in row_coeff.

The invariant identifies the degree-r coefficient of R(n+1,k+1) with
[z^n] A(z)^r B_(k+1)(z), where B_k(z) has coefficients a(j+k).
Splitting B_k into its constant term and z times B_(k+1) gives the two
recursion terms, corresponding to a final composition part of one or at least two.
-/

import D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries
import Mathlib.Algebra.Polynomial.OfFn

set_option autoImplicit false
noncomputable section

namespace D5.S1.Recurrence.Algebraic.KurkovConvolutionRowRecursion

open Finset Polynomial PowerSeries
open scoped BigOperators Polynomial

variable {K : Type*} [CommSemiring K]

def sourceSeries (a : ℕ → K) : PowerSeries K :=
  PowerSeries.mk (fun j => if j = 0 then 0 else a j)

def IsSourceSeries (a : ℕ → K) (A : PowerSeries K) : Prop :=
  A = sourceSeries a

def T (A : PowerSeries K) (n r : ℕ) : K :=
  PowerSeries.coeff n (A ^ r)

def rowPolynomial (A : PowerSeries K) (n : ℕ) : Polynomial K :=
  ∑ r ∈ range (n + 1), Polynomial.C (T A n r) * Polynomial.X ^ r

def kurkovR (a : ℕ → K) : ℕ → ℕ → Polynomial K
  | 0, _ => 0
  | 1, 0 => 0
  | 1, k + 1 => Polynomial.C (a (k + 1))
  | _n + 2, 0 => 0
  | n + 2, k + 1 =>
      kurkovR a (n + 1) (k + 2) +
        Polynomial.X * Polynomial.C (a (k + 1)) * kurkovR a (n + 1) 1
termination_by n _ => n
decreasing_by
  all_goals simp_wf

def claim : Prop :=
  ∀ (K : Type*) [CommSemiring K] (a : ℕ → K),
    ∃ A : PowerSeries K,
      IsSourceSeries a A ∧
        ∀ n : ℕ, 1 ≤ n → rowPolynomial A n =
          Polynomial.X * kurkovR a n 1

private theorem source_eq (a : ℕ → K) :
    sourceSeries a = PowerSeries.X * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a 1 := by
  simpa [sourceSeries, D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail,
    Nat.add_comm] using PowerSeries.eq_X_mul_shift_add_const (sourceSeries a)

private theorem tail_split (a : ℕ → K) (k : ℕ) :
    D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a k = PowerSeries.X * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a (k + 1) + PowerSeries.C (a k) := by
  simpa [D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    PowerSeries.eq_X_mul_shift_add_const (D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a k)

private theorem source_pow_coeff_succ (a : ℕ → K) (n r : ℕ) :
    PowerSeries.coeff (n + 1) (sourceSeries a ^ (r + 1)) =
      PowerSeries.coeff n (sourceSeries a ^ r * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a 1) := by
  rw [pow_succ, source_eq a]
  rw [show (PowerSeries.X * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a 1) ^ r *
      (PowerSeries.X * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a 1) =
      PowerSeries.X * ((PowerSeries.X * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a 1) ^ r * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a 1) by exact mul_left_comm _ _ _]
  exact PowerSeries.coeff_succ_X_mul _ _

private theorem source_pow_coeff_zero (a : ℕ → K) (n r : ℕ) (h : n < r) :
    PowerSeries.coeff n (sourceSeries a ^ r) = 0 := by
  rw [source_eq, mul_pow, PowerSeries.coeff_X_pow_mul', ite_eq_right (Nat.not_le.mpr h)]

private theorem kurkov_coeff (a : ℕ → K) (n k r : ℕ) :
    (kurkovR a (n + 1) (k + 1)).coeff r =
      PowerSeries.coeff n (sourceSeries a ^ r * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a (k + 1)) := by
  induction n generalizing k r with
  | zero =>
    cases r with
    | zero => simp [kurkovR, D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail]
    | succ r =>
      simp [kurkovR, D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail, sourceSeries,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_succ]
  | succ n ih =>
    rw [kurkovR]
    cases r with
    | zero =>
      rw [Polynomial.coeff_add, mul_assoc, Polynomial.coeff_X_mul_zero, add_zero, ih]
      rw [tail_split a (k + 1)]
      simp
    | succ r =>
      rw [Polynomial.coeff_add, mul_assoc, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, ih, ih]
      rw [tail_split a (k + 1), mul_add]
      rw [show sourceSeries a ^ (r + 1) *
          (PowerSeries.X * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a (k + 1 + 1)) =
          PowerSeries.X * (sourceSeries a ^ (r + 1) * D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail a (k + 1 + 1)) by exact mul_left_comm _ _ _]
      rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul_C,
        source_pow_coeff_succ]
      ac_rfl

private theorem row_as_of_fn (A : PowerSeries K) (n : ℕ) :
    rowPolynomial A n = @Polynomial.ofFn K _ (Classical.decEq K) (n + 1)
      (fun i => T A n i.val) := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [rowPolynomial, Polynomial.C_mul_X_pow_eq_monomial]
  exact (Fin.sum_univ_eq_sum_range
    (fun r => Polynomial.monomial r (T A n r)) (n + 1)).symm

private theorem row_coeff (A : PowerSeries K) (n r : ℕ) :
    (rowPolynomial A n).coeff r = if r < n + 1 then T A n r else 0 := by
  classical
  rw [row_as_of_fn]
  by_cases h : r < n + 1
  · simpa only [ite_eq_left h] using
      (Polynomial.ofFn_coeff_eq_val_of_lt (fun i : Fin (n + 1) => T A n i.val) h)
  · simpa only [ite_eq_right h] using
      (Polynomial.ofFn_coeff_eq_zero_of_ge (fun i : Fin (n + 1) => T A n i.val)
        (Nat.le_of_not_gt h))

theorem result : D5.S1.Recurrence.Algebraic.KurkovConvolutionRowRecursion.claim := by
  intro K _ a
  refine ⟨sourceSeries a, rfl, ?_⟩
  intro n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  ext r
  rw [row_coeff]
  cases r with
  | zero => simp [T, PowerSeries.coeff_one]
  | succ r =>
    rw [Polynomial.coeff_X_mul, kurkov_coeff a n 0 r]
    simp only [Nat.zero_add]
    by_cases h : r + 1 < n + 1 + 1
    · rw [ite_eq_left h]
      exact source_pow_coeff_succ a n r
    · rw [ite_eq_right h, ← source_pow_coeff_succ]
      exact (source_pow_coeff_zero a (n + 1) (r + 1) (by omega)).symm

end D5.S1.Recurrence.Algebraic.KurkovConvolutionRowRecursion
