/- GID: D5/S1/Recurrence/StephanTriangleSecondColumn
   generality: I
   mirror-B: D5/B/S1/Recurrence/StephanTriangleSecondColumn
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: The second column of Kimberling's row-sum triangle is shifted OEIS A006183. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators

namespace D5.S1.Recurrence.StephanTriangleSecondColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The sum of row `n`, whose columns are indexed from zero through `n`. -/
def rowSum (T : ℕ → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), T n k

/-- The defining equations of the triangular array in OEIS A054090. -/
def IsA054090Triangle (T : ℕ → ℕ → ℤ) : Prop :=
  (∀ n, T n 0 = 1) ∧
  (∀ n, T (n + 1) 1 = rowSum T n) ∧
  ∀ n k, 2 ≤ k → k ≤ n →
    T n k = T n (k - 1) - (-1 : ℤ) ^ k * rowSum T (n - k)

/-- The A006183 recurrence after shifting its offset-one indexing to `B j = a (j - 1)`. -/
def IsShiftedA006183 (B : ℕ → ℤ) : Prop :=
  B 1 = 1 ∧ B 2 = 2 ∧
  ∀ j, 3 ≤ j →
    B j = (j : ℤ) * B (j - 1) + (3 - (j : ℤ)) * B (j - 2)

private theorem cross_row (T : ℕ → ℕ → ℤ) (hT : IsA054090Triangle T)
    (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) :
    T n j = T (n + 1) 1 - T (n + 1) (j + 1) := by
  induction j, hj using Nat.le_induction with
  | base =>
      have hn1 : n - 1 + 1 = n := by omega
      have hfirst : T n 1 = rowSum T (n - 1) := by
        simpa only [hn1] using hT.2.1 (n - 1)
      have hstep := hT.2.2 (n + 1) 2 (by omega) (by omega)
      norm_num only [Nat.add_sub_cancel] at hstep
      rw [show n + 1 - 2 = n - 1 by omega] at hstep
      rw [hfirst, hstep]
      ring
  | succ j hj ih =>
      have hjn' : j ≤ n := by omega
      have hleft := hT.2.2 n (j + 1) (by omega) (by omega)
      have hright := hT.2.2 (n + 1) (j + 2) (by omega) (by omega)
      norm_num only [Nat.add_sub_cancel] at hleft hright
      rw [show j + 2 - 1 = j + 1 by omega] at hright
      rw [hleft, hright, ih hjn']
      have hsub : n - (j + 1) = n + 1 - (j + 2) := by omega
      rw [hsub]
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring

/-- Every A054090 triangle has row sums satisfying the A054091 first-order recurrence. -/
theorem rowSum_succ (T : ℕ → ℕ → ℤ) (hT : IsA054090Triangle T) (n : ℕ) :
    rowSum T (n + 1) = (n : ℤ) * rowSum T n + 2 := by
  cases n with
  | zero =>
      simp [rowSum, sum_range_succ, hT.1, hT.2.1]
  | succ n =>
      have hcross (j : ℕ) (hj : j < n + 1) :
          T (n + 1) (j + 1) = T (n + 2) 1 - T (n + 2) (j + 2) :=
        cross_row T hT (n + 1) (j + 1) (by omega) (by omega) (by omega)
      have hsum :
          (∑ j ∈ range (n + 1), T (n + 1) (j + 1)) =
            ∑ j ∈ range (n + 1),
              (rowSum T (n + 1) - T (n + 2) (j + 2)) := by
        apply sum_congr rfl
        intro j hj
        rw [hcross j (mem_range.mp hj), hT.2.1]
      have hrow :
          rowSum T (n + 1) =
            1 + ∑ j ∈ range (n + 1),
              (rowSum T (n + 1) - T (n + 2) (j + 2)) := by
        conv_lhs => rw [rowSum]
        rw [sum_range_succ', hT.1, hsum]
        ring
      have hnext :
          rowSum T (n + 2) =
            1 + rowSum T (n + 1) + ∑ j ∈ range (n + 1), T (n + 2) (j + 2) := by
        rw [rowSum, sum_range_succ', sum_range_succ']
        simp only [hT.1, hT.2.1]
        ring
      rw [hrow] at hnext
      simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hnext
      ring_nf at hnext
      rw [Nat.add_comm n 2, hnext, Nat.add_comm 1 n]
      ring

private theorem shifted_eq_row_difference (T : ℕ → ℕ → ℤ) (B : ℕ → ℤ)
    (hT : IsA054090Triangle T) (hB : IsShiftedA006183 B) :
    ∀ j, 1 ≤ j → B j = rowSum T j - rowSum T (j - 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      by_cases hj1 : j = 1
      · subst j
        rw [hB.1, rowSum_succ T hT 0]
        simp [rowSum, hT.1]
      by_cases hj2 : j = 2
      · subst j
        rw [hB.2.1, rowSum_succ T hT 1, rowSum_succ T hT 0]
        simp [rowSum, hT.1]
      have hj3 : 3 ≤ j := by omega
      rw [hB.2.2 j hj3, ih (j - 1) (by omega) (by omega),
        ih (j - 2) (by omega) (by omega)]
      have hsj := rowSum_succ T hT (j - 1)
      have hsj1 := rowSum_succ T hT (j - 2)
      have hsj2 := rowSum_succ T hT (j - 3)
      have h1 : j - 1 + 1 = j := by omega
      have h2 : j - 2 + 1 = j - 1 := by omega
      have h3 : j - 3 + 1 = j - 2 := by omega
      have hm1 : j - 1 - 1 = j - 2 := by omega
      have hm2 : j - 2 - 1 = j - 3 := by omega
      have hc1 : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
      have hc2 : ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 := by omega
      have hc3 : ((j - 3 : ℕ) : ℤ) = (j : ℤ) - 3 := by omega
      rw [h1] at hsj
      rw [h2] at hsj1
      rw [h3] at hsj2
      rw [hm1, hm2]
      rw [hc1] at hsj
      rw [hc2] at hsj1
      rw [hc3] at hsj2
      rw [hsj, hsj1, hsj2]
      ring

/-- Ralf Stephan's A054096 conjecture: column two is A006183 shifted right. -/
theorem result (T : ℕ → ℕ → ℤ) (B : ℕ → ℤ)
    (hT : IsA054090Triangle T) (hB : IsShiftedA006183 B) :
    ∀ n, 2 ≤ n → T n 2 = B (n - 1) := by
  intro n hn
  have hstep := hT.2.2 n 2 (by omega) (by omega)
  have hfirst : T n 1 = rowSum T (n - 1) := by
    simpa only [show n - 1 + 1 = n by omega] using hT.2.1 (n - 1)
  have hBdiff := shifted_eq_row_difference T B hT hB (n - 1) (by omega)
  rw [hstep, hfirst]
  norm_num
  rw [show n - 2 = n - 1 - 1 by omega, ← hBdiff]

#print axioms rowSum
#print axioms IsA054090Triangle
#print axioms IsShiftedA006183
#print axioms rowSum_succ
#print axioms result

end D5.S1.Recurrence.StephanTriangleSecondColumn
