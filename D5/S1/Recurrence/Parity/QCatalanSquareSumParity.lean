/- GID: D5/S1/Recurrence/Parity/QCatalanSquareSumParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/QCatalanSquareSumParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The q-Catalan row recursion reduces its square sum parity to binary Catalan support. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

open Finset PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Parity.QCatalanSquareSumParity

/-- The Carlitz-Riordan q-Catalan row polynomial, defined by coefficient extraction
from its generating-function equation. -/
noncomputable def qCatalanRow : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1),
      Polynomial.monomial i 1 * qCatalanRow i * qCatalanRow (n - i)
termination_by n => n
decreasing_by all_goals omega

/-- The coefficient triangle of the Carlitz-Riordan q-Catalan row polynomials. -/
noncomputable def qCatalanCoeff (n k : ℕ) : ℤ := (qCatalanRow n).coeff k

/-- The specialization of the nth row polynomial at q=1. -/
noncomputable def rowSum (n : ℕ) : ℤ := (qCatalanRow n).eval 1

/-- The sum of squares across the finite nth q-Catalan row. -/
noncomputable def squareSum (n : ℕ) : ℤ :=
  ∑ k ∈ range (n * (n - 1) / 2 + 1), qCatalanCoeff n k ^ 2

/-- Coefficient extraction from `A(x,q)=1+x A(qx,q) A(x,q)` gives the row recurrence. -/
theorem qCatalanRow_succ (n : ℕ) :
    qCatalanRow (n + 1) = ∑ i : Fin (n + 1),
      Polynomial.monomial i 1 * qCatalanRow i * qCatalanRow (n - i) := by
  rw [qCatalanRow]

private theorem rowSum_zero : rowSum 0 = 1 := by
  simp [rowSum, qCatalanRow]

private theorem rowSum_succ (n : ℕ) :
    rowSum (n + 1) = ∑ i : Fin (n + 1), rowSum i * rowSum (n - i) := by
  simp [rowSum, qCatalanRow, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_monomial]

private noncomputable def rowSumSeries : PowerSeries ℤ := mk rowSum

private theorem rowSumSeries_equation :
    rowSumSeries = 1 + X * rowSumSeries ^ 2 := by
  ext n
  cases n with
  | zero => simp [rowSumSeries, rowSum_zero, coeff_zero_eq_constantCoeff]
  | succ n =>
      rw [rowSumSeries, coeff_mk, rowSum_succ, map_add, coeff_succ_X_mul,
        pow_two, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        ← Fin.sum_univ_eq_sum_range]
      simp

private noncomputable def shiftedRowSumSeries : PowerSeries ℤ := X * rowSumSeries

private theorem shiftedRowSumSeries_equation :
    shiftedRowSumSeries = X + shiftedRowSumSeries ^ 2 := by
  change X * rowSumSeries = X + (X * rowSumSeries) ^ 2
  calc
    X * rowSumSeries = X * (1 + X * rowSumSeries ^ 2) := by
      exact congrArg (X * ·) rowSumSeries_equation
    _ = X + (X * rowSumSeries) ^ 2 := by ring

private theorem shiftedRowSumSeries_eq_catalan :
    shiftedRowSumSeries =
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries := by
  apply D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalan_unique
  · simp [shiftedRowSumSeries]
  · exact shiftedRowSumSeries_equation

/-- At q=1, the row sum is the correspondingly shifted Catalan coefficient. -/
theorem rowSum_eq_catalan (n : ℕ) :
    rowSum n = coeff (n + 1)
      D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries := by
  rw [← shiftedRowSumSeries_eq_catalan, shiftedRowSumSeries, coeff_succ_X_mul,
    rowSumSeries, coeff_mk]

private theorem choose_two_add_le (a b : ℕ) :
    a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hb : (b + 1).choose 2 = b + b.choose 2 := by
        rw [Nat.choose_succ_succ]
        simp
      have hab : (a + b + 1).choose 2 = a + b + (a + b).choose 2 := by
        rw [Nat.choose_succ_succ]
        simp
      rw [show a + (b + 1) = a + b + 1 by omega, hb, hab]
      omega

private theorem qCatalanRow_natDegree_le (n : ℕ) :
    (qCatalanRow n).natDegree ≤ n.choose 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [qCatalanRow]
      | succ n =>
          rw [qCatalanRow]
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro i _hi
          have hil : (qCatalanRow i).natDegree ≤ (i : ℕ).choose 2 := ih i i.isLt
          have hir : (qCatalanRow (n - i)).natDegree ≤ (n - i).choose 2 :=
            ih (n - i) (by omega)
          calc
            (Polynomial.monomial i 1 * qCatalanRow i * qCatalanRow (n - i)).natDegree
                ≤ (Polynomial.monomial i 1 * qCatalanRow i).natDegree +
                    (qCatalanRow (n - i)).natDegree := Polynomial.natDegree_mul_le
            _ ≤ ((Polynomial.monomial (R := ℤ) i 1).natDegree +
                  (qCatalanRow i).natDegree) +
                  (qCatalanRow (n - i)).natDegree :=
              Nat.add_le_add_right
                (Polynomial.natDegree_mul_le
                  (p := Polynomial.monomial (R := ℤ) (i : ℕ) 1) (q := qCatalanRow i)) _
            _ ≤ (i : ℕ) + (i : ℕ).choose 2 + (n - i).choose 2 := by
              exact Nat.add_le_add (Nat.add_le_add (by simp) hil) hir
            _ = ((i : ℕ) + 1).choose 2 + (n - i).choose 2 := by
              simp [Nat.choose_succ_succ, Nat.choose_one_right]
            _ ≤ (((i : ℕ) + 1) + (n - i)).choose 2 := choose_two_add_le _ _
            _ = (n + 1).choose 2 := congrArg (fun m : ℕ => m.choose 2) (by omega)

private theorem rowSum_eq_coeff_sum (n : ℕ) :
    rowSum n =
      ∑ k ∈ range (n * (n - 1) / 2 + 1), qCatalanCoeff n k := by
  have hd : (qCatalanRow n).natDegree ≤ n * (n - 1) / 2 := by
    simpa only [← Nat.choose_two_right] using qCatalanRow_natDegree_le n
  rw [rowSum, Polynomial.eval_eq_sum_range'
    (n := n * (n - 1) / 2 + 1) (Nat.lt_succ_of_le hd) 1]
  simp [qCatalanCoeff]

/-- Modulo two, the q-Catalan row's square sum is its Catalan row sum. -/
theorem squareSum_mod_two_eq_catalan (n : ℕ) :
    (squareSum n : ZMod 2) = coeff (n + 1)
      (D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries.map
        (Int.castRingHom (ZMod 2))) := by
  calc
    (squareSum n : ZMod 2) =
        ∑ k ∈ range (n * (n - 1) / 2 + 1), (qCatalanCoeff n k : ZMod 2) ^ 2 := by
      simp [squareSum]
    _ = ∑ k ∈ range (n * (n - 1) / 2 + 1), (qCatalanCoeff n k : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact ZMod.pow_card _
    _ = (rowSum n : ZMod 2) := by
      rw [rowSum_eq_coeff_sum]
      simp
    _ = coeff (n + 1)
        (D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries.map
          (Int.castRingHom (ZMod 2))) := by
      simpa only [coeff_map, Int.coe_castRingHom] using congrArg (Int.castRingHom (ZMod 2))
        (rowSum_eq_catalan n)

/-- The square sum of the nth Carlitz-Riordan q-Catalan row is odd exactly one below
a power of two. -/
theorem hanna_conjecture (n : ℕ) :
    Odd (squareSum n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [← ZMod.intCast_eq_one_iff_odd, squareSum_mod_two_eq_catalan,
    D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.binary_catalan]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hp : 0 < 2 ^ k := pow_pos (by omega) k
    omega

#print axioms qCatalanRow_succ
#print axioms rowSum_eq_catalan
#print axioms squareSum_mod_two_eq_catalan
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.QCatalanSquareSumParity
