/- GID: D5/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/FactorialConvolutionFirstColumn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A factorial convolution invariant identifies the first column. -/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
# The first-column bridge for OEIS A370380

The array is defined exactly by its row recurrence. The sequence `a` in the
final theorem is abstract: it is assumed to satisfy Bowen's factorial
convolution and `a 1 = 1`. In particular, this module does not define
indecomposable permutations or prove that their cardinalities satisfy Bowen's
recurrence; that permutation interpretation remains a hypothesis here.

The two-variable factorial convolution invariant is the essential step. Its
prefix sum telescopes between adjacent ascending factorials, and its
specialization at column zero gives the same triangular convolution as
Bowen's recurrence.
-/

namespace D5.S1.Recurrence.Invariants.FactorialConvolutionFirstColumn

open Finset
open scoped BigOperators

/-- The A370380 array, with rows indexed first and columns indexed second. -/
def array : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k =>
      (k + 2) * array n (k + 1) + ∑ j ∈ range (k + 1), array n j

/-- The prefix sum needed by the convolution invariant telescopes to one
ascending factorial. -/
private theorem ascFactorial_prefix_sum (n k : ℕ) :
    (∑ j ∈ range k, (n + 1) * Nat.ascFactorial (j + 2) n) + (n + 1).factorial =
      Nat.ascFactorial (k + 1) (n + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hshift :
          Nat.ascFactorial (k + 1) (n + 1) =
            (k + 1) * Nat.ascFactorial (k + 2) n := by
        rw [Nat.ascFactorial_succ, Nat.succ_ascFactorial]
      calc
        (∑ j ∈ range (k + 1), (n + 1) * Nat.ascFactorial (j + 2) n) +
              (n + 1).factorial =
            ((∑ j ∈ range k, (n + 1) * Nat.ascFactorial (j + 2) n) +
              (n + 1).factorial) +
                (n + 1) * Nat.ascFactorial (k + 2) n := by
                  rw [sum_range_succ]
                  ac_rfl
        _ = Nat.ascFactorial (k + 1) (n + 1) +
              (n + 1) * Nat.ascFactorial (k + 2) n := by rw [ih]
        _ = Nat.ascFactorial (k + 2) (n + 1) := by
              rw [hshift, Nat.ascFactorial_succ]
              ring

private theorem leading_convolution_term (n k : ℕ) :
    (k + 2) * ((n + 1) * Nat.ascFactorial (k + 3) n) =
      (n + 1) * Nat.ascFactorial (k + 2) (n + 1) := by
  calc
    (k + 2) * ((n + 1) * Nat.ascFactorial (k + 3) n) =
        (n + 1) * ((k + 2) * Nat.ascFactorial (k + 3) n) := by ring
    _ = (n + 1) * ((k + 2 + n) * Nat.ascFactorial (k + 2) n) := by
      rw [Nat.succ_ascFactorial]
    _ = (n + 1) * Nat.ascFactorial (k + 2) (n + 1) := by
      rw [Nat.ascFactorial_succ]

/-- The factorial convolution of every row is an ascending factorial:
`sum_{r=0}^n r! A(n-r,k) = (n+1) (k+2)^(ascending n)`. -/
theorem factorial_convolution_invariant (n k : ℕ) :
    ∑ r ∈ range (n + 1), r.factorial * array (n - r) k =
      (n + 1) * Nat.ascFactorial (k + 2) n := by
  induction n generalizing k with
  | zero => simp [array]
  | succ n ih =>
      have hrecur :
          ∑ r ∈ range (n + 1), r.factorial * array (n + 1 - r) k =
            ∑ r ∈ range (n + 1),
              r.factorial *
                ((k + 2) * array (n - r) (k + 1) +
                  ∑ j ∈ range (k + 1), array (n - r) j) := by
        apply sum_congr rfl
        intro r hr
        have hrle : r ≤ n := Nat.le_of_lt_succ (mem_range.mp hr)
        rw [show n + 1 - r = (n - r) + 1 by omega, array]
      have hfirst :
          ∑ r ∈ range (n + 1),
              r.factorial * ((k + 2) * array (n - r) (k + 1)) =
            (k + 2) *
              ∑ r ∈ range (n + 1), r.factorial * array (n - r) (k + 1) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro r _
        ring
      have hsecond :
          ∑ r ∈ range (n + 1),
              r.factorial * (∑ j ∈ range (k + 1), array (n - r) j) =
            ∑ j ∈ range (k + 1),
              ∑ r ∈ range (n + 1), r.factorial * array (n - r) j := by
        simp_rw [mul_sum]
        rw [sum_comm]
      calc
        ∑ r ∈ range (n + 1 + 1), r.factorial * array (n + 1 - r) k =
            (∑ r ∈ range (n + 1), r.factorial * array (n + 1 - r) k) +
              (n + 1).factorial := by
                rw [sum_range_succ]
                simp [array]
        _ = (k + 2) *
              (∑ r ∈ range (n + 1), r.factorial * array (n - r) (k + 1)) +
            (∑ j ∈ range (k + 1),
              ∑ r ∈ range (n + 1), r.factorial * array (n - r) j) +
              (n + 1).factorial := by
                rw [hrecur]
                simp_rw [mul_add]
                rw [sum_add_distrib, hfirst, hsecond]
        _ = (k + 2) * ((n + 1) * Nat.ascFactorial (k + 3) n) +
            (∑ j ∈ range (k + 1),
              (n + 1) * Nat.ascFactorial (j + 2) n) + (n + 1).factorial := by
                rw [ih (k + 1)]
                simp_rw [ih]
        _ = (n + 1) * Nat.ascFactorial (k + 2) (n + 1) +
            (∑ j ∈ range (k + 1),
              (n + 1) * Nat.ascFactorial (j + 2) n) + (n + 1).factorial := by
                rw [leading_convolution_term]
        _ = (n + 2) * Nat.ascFactorial (k + 2) (n + 1) := by
              rw [add_assoc, ascFactorial_prefix_sum n (k + 1)]
              ring

/-- Any natural sequence with `a(1)=1` and Bowen's factorial convolution is
the first column of the A370380 array, shifted by two indices. -/
theorem factorial_convolution_first_column
    (a : ℕ → ℕ)
    (ha_one : a 1 = 1)
    (hbowen : ∀ m, 1 ≤ m →
      m.factorial = ∑ r ∈ range m, r.factorial * a (m - r)) :
    ∀ n, array n 0 = a (n + 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have htwo : Nat.ascFactorial 2 n = (n + 1).factorial := by
        simpa [Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 n
      have harray :
          ∑ r ∈ range (n + 1), r.factorial * array (n - r) 0 =
            (n + 1) * (n + 1).factorial := by
        simpa [htwo] using factorial_convolution_invariant n 0
      have hbowen_split :
          (n + 2).factorial =
            (∑ r ∈ range (n + 1), r.factorial * a (n + 2 - r)) +
              (n + 1).factorial := by
        simpa [sum_range_succ, ha_one] using hbowen (n + 2) (by omega)
      have hfactorial :
          (n + 2).factorial =
            (n + 1) * (n + 1).factorial + (n + 1).factorial := by
        rw [Nat.factorial_succ]
        ring
      have ha :
          ∑ r ∈ range (n + 1), r.factorial * a (n + 2 - r) =
            (n + 1) * (n + 1).factorial := by
        exact Nat.add_right_cancel (hbowen_split.symm.trans hfactorial)
      have htail :
          ∑ r ∈ range n, (r + 1).factorial * array (n - (r + 1)) 0 =
            ∑ r ∈ range n, (r + 1).factorial * a (n + 2 - (r + 1)) := by
        apply sum_congr rfl
        intro r hr
        have hrlt : r < n := mem_range.mp hr
        have hsmaller : n - (r + 1) < n := Nat.sub_lt (by omega) (by omega)
        rw [ih (n - (r + 1)) hsmaller]
        congr 2
        omega
      rw [sum_range_succ'] at harray ha
      simp only [Nat.factorial_zero, one_mul, Nat.sub_zero] at harray ha
      rw [htail] at harray
      exact Nat.add_left_cancel (harray.trans ha.symm)

private def bowenModel : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => array n 0

private theorem bowenModel_recurrence (m : ℕ) (hm : 1 ≤ m) :
    m.factorial = ∑ r ∈ range m, r.factorial * bowenModel (m - r) := by
  rcases m with _ | m
  · omega
  rcases m with _ | n
  · simp [bowenModel]
  · have hprefix :
        ∑ r ∈ range (n + 1), r.factorial * bowenModel (n + 2 - r) =
          ∑ r ∈ range (n + 1), r.factorial * array (n - r) 0 := by
      apply sum_congr rfl
      intro r hr
      have hrle : r ≤ n := Nat.le_of_lt_succ (mem_range.mp hr)
      rw [show n + 2 - r = (n - r) + 2 by omega, bowenModel]
    have htwo : Nat.ascFactorial 2 n = (n + 1).factorial := by
      simpa [Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 n
    rw [sum_range_succ, hprefix, factorial_convolution_invariant]
    simp [bowenModel, Nat.factorial_succ, htwo]
    ring

example : bowenModel 1 = 1 ∧
    ∀ m, 1 ≤ m → m.factorial = ∑ r ∈ range m, r.factorial * bowenModel (m - r) :=
  ⟨rfl, bowenModel_recurrence⟩

example : array 2 0 = 13 ∧ bowenModel 4 = 13 := by
  norm_num [array, bowenModel, sum_range_succ]

example : (fun _ : ℕ => 0) 1 ≠ 1 ∧ array 0 0 ≠ (fun _ : ℕ => 0) 2 := by
  norm_num [array]

#print axioms factorial_convolution_invariant
#print axioms factorial_convolution_first_column

end D5.S1.Recurrence.Invariants.FactorialConvolutionFirstColumn
