/- GID: D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kurkov's weighted-ballot formula for the A107667 triangle. -/

/-
Public theorem result:
  proof_shape: content (first-return induction followed by strong induction in n).
  escape_witness: first_return, the off-diagonal shifted-parameter convolution.
  admission_basis: open-problem-resolution (#21639; Proved).
  Direct frozen dependencies: none.
Private theorem b_zero:
  proof_shape: bind-only (base-rule projection and normalization).
  consumers: first_return, result.
Private theorem b_above:
  proof_shape: bind-only (zero-extension simplification).
  consumers: b_step, first_return, result.
Private theorem b_step:
  proof_shape: bind-only (interior and diagonal rules, split by y = x).
  consumers: first_return.
Private theorem first_return:
  proof_shape: content (nested induction with the shifted-weight convolution).
  escape_witness: first_return, its conclusion produced by nested induction.
  consumer: result.
All private helpers have direct frozen dependencies: none.
The source predicates and claim retain the recurrences from #21639.
The proof uses Set.indicator on Set.Iic for the zero extension of the table.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21710
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

import Mathlib.Order.Interval.Finset.Nat

namespace D5.S1.Recurrence.Algebraic.KurkovA107667WeightedBallot

open scoped BigOperators

/-- The zero-indexed lower triangular matrix in the NAME of OEIS A107667.
The finite sum is the (a,b+1) entry of T^2, for b < a. -/
def IsSourceTriangle (T : ℕ → ℕ → ℕ) : Prop :=
  (∀ (a b : ℕ), a < b → T a b = 0) ∧
  (∀ (a : ℕ), T a a = a + 1) ∧
  (∀ (a b : ℕ), b < a →
    T a b = ∑ j ∈ Finset.Icc (b + 1) a, T a j * T j (b + 1))

/-- Kurkov's three-argument P, on r >= k >= 1. This is not the
unrelated conjugating matrix P in the earlier FORMULA line.
The base rule includes P(1,1,m)=1; the diagonal rule starts at r=2. -/
def IsPTable (P : ℕ → ℕ → ℕ → ℕ) : Prop :=
  (∀ (r m : ℕ), 1 ≤ r → P r 1 m = 1) ∧
  (∀ (r k m : ℕ), 1 < k → k < r →
    P r k m = P (r - 1) k m + (r + m) * P r (k - 1) m) ∧
  (∀ (r m : ℕ), 2 ≤ r →
    P r r m = (r + m) * P r (r - 1) m)

/-- The entire conjecture in the FORMULA line of approved revision 25.
Both tables are constrained by precisely their source recurrences. -/
def claim : Prop :=
  ∀ (T : ℕ → ℕ → ℕ) (P : ℕ → ℕ → ℕ → ℕ),
    IsSourceTriangle T → IsPTable P →
      ∀ (n m : ℕ), T (n + m) m = (n + m + 1) * P (n + 1) (n + 1) m

end D5.S1.Recurrence.Algebraic.KurkovA107667WeightedBallot

namespace D5.S1.Recurrence.Algebraic.KurkovA107667WeightedBallot
open scoped BigOperators

set_option maxHeartbeats 1000000

local macro "B" P:term:max m:term:max x:term:max y:term:max : term =>
  `(Set.indicator (Set.Iic $x) (fun z => $P ($x + 1) (z + 1) $m) $y)

variable {P : ℕ → ℕ → ℕ → ℕ}

private theorem b_zero (hP : IsPTable P) (m x : ℕ) : B P m x 0 = 1 := by
  rw [Set.indicator_of_mem (show 0 ∈ Set.Iic x from Nat.zero_le x)]
  exact hP.1 (x + 1) m (by omega)

private theorem b_above (m x y : ℕ) (h : x < y) : B P m x y = 0 := by
  exact Set.indicator_of_notMem (show y ∉ Set.Iic x from Nat.not_le.mpr h) _

private theorem b_step (hP : IsPTable P) (m x y : ℕ) (hy : y ≤ x) :
    B P m (x + 1) (y + 1) =
      B P m x (y + 1) + (m + x + 2) * B P m (x + 1) y := by
  by_cases he : y = x
  · subst y
    rw [b_above m x (x + 1) (by omega)]
    simp only [zero_add, Set.indicator_apply, Set.mem_Iic, Nat.le_refl, ↓reduceIte]
    have hh := hP.2.2 (x + 1 + 1) m (by omega)
    simpa [show x + 1 + 1 - 1 = x + 1 by omega,
      show x + 1 + 1 + m = m + x + 2 by omega] using hh
  · have hlt : y + 1 ≤ x := by omega
    simp only [Set.indicator_apply, Set.mem_Iic, show y + 1 ≤ x + 1 by omega, hlt,
      show y ≤ x + 1 by omega, ↓reduceIte]
    have hh := hP.2.1 (x + 1 + 1) (y + 1 + 1) m (by omega) (by omega)
    simpa [show x + 1 + 1 - 1 = x + 1 by omega,
      show y + 1 + 1 - 1 = y + 1 by omega,
      show x + 1 + 1 + m = m + x + 2 by omega] using hh


private theorem first_return (hP : IsPTable P) (x y m : ℕ) (h : y ≤ x) :
    B P m (x + 1) (y + 1) = B P (m + 1) x (y + 1) +
      ∑ i ∈ Finset.range (y + 1),
        (m + i + 2) * B P (m + 1) i i * B P (m + i + 1) (x - i) (y - i) := by
  induction x generalizing y m with
  | zero =>
    have hy : y = 0 := by exact Nat.eq_zero_of_le_zero h
    subst y
    rw [b_step hP m 0 0 (by omega)]
    simp [-Set.indicator_of_mem, -Set.indicator_of_notMem, b_above, b_zero hP]
  | succ x ih =>
    induction y with
    | zero =>
      rw [b_step hP m (x + 1) 0 (by omega), ih 0 m (by omega),
        b_step hP (m + 1) x 0 (by omega)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.sub_zero, b_zero hP, mul_one, Nat.add_zero]
      ring
    | succ y ihy =>
      by_cases he : y = x
      · subst y
        rw [b_step hP m (x + 1) (x + 1) (by omega),
          b_above m (x + 1) (x + 1 + 1) (by omega), zero_add,
          ihy (by omega), b_above (m + 1) (x + 1) (x + 1 + 1) (by omega),
          zero_add]
        conv_rhs => rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, b_zero hP, mul_one]
        rw [Nat.mul_add, Finset.mul_sum]
        rw [add_comm ((m + (x + 1) + 2) * B P (m + 1) (x + 1) (x + 1))]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro i hi
          have hi' : i ≤ x := by exact Finset.mem_range_succ_iff.mp hi
          have hs := b_step hP (m + i + 1) (x - i) (x - i) (by omega)
          rw [b_above (m + i + 1) (x - i) (x - i + 1) (by omega), zero_add] at hs
          have hx : x + 1 - i = x - i + 1 := by exact Nat.sub_add_comm hi'
          rw [hx, hs]
          have hc : m + i + 1 + (x - i) + 2 = m + (x + 1) + 2 := by omega
          rw [hc]
          ring
        · ring
      · have hy : y + 1 ≤ x := by omega
        rw [b_step hP m (x + 1) (y + 1) (by omega), ih (y + 1) m hy,
          ihy (by omega), b_step hP (m + 1) x (y + 1) hy]
        rw [Finset.sum_range_succ (n := y + 1), Finset.sum_range_succ (n := y + 1)]
        simp only [Nat.sub_self, b_zero hP, mul_one]
        rw [Nat.mul_add]
        have hsum :
            (∑ i ∈ Finset.range (y + 1),
              (m + i + 2) * B P (m + 1) i i * B P (m + i + 1) (x - i) (y + 1 - i)) +
            (m + (x + 1) + 2) *
              (∑ i ∈ Finset.range (y + 1),
                (m + i + 2) * B P (m + 1) i i * B P (m + i + 1) (x + 1 - i) (y - i)) =
            ∑ i ∈ Finset.range (y + 1),
              (m + i + 2) * B P (m + 1) i i * B P (m + i + 1) (x + 1 - i) (y + 1 - i) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i ≤ y := by exact Finset.mem_range_succ_iff.mp hi
          have hx : x + 1 - i = x - i + 1 := by exact Nat.sub_add_comm (by omega)
          have hyi : y + 1 - i = y - i + 1 := by exact Nat.sub_add_comm hi'
          have hc : m + i + 1 + (x - i) + 2 = m + (x + 1) + 2 := by omega
          rw [hx, hyi, b_step hP (m + i + 1) (x - i) (y - i) (by omega), hc]
          ring
        rw [show m + 1 + x + 2 = m + (x + 1) + 2 by omega]
        omega


theorem result : claim := by
  intro T P hT hP n
  have hb : ∀ n m, T (n + m) m = (n + m + 1) * B P m n n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m
      cases n with
      | zero =>
        simp only [Nat.zero_add, hT.2.1, b_zero hP, mul_one]
      | succ n =>
        rw [hT.2.2 (n + 1 + m) m (by omega)]
        rw [first_return hP n n m (by omega),
          b_above (m + 1) n (n + 1) (by omega), zero_add, Finset.mul_sum]
        symm
        apply Finset.sum_bij (fun i _ => m + i + 1)
        · intro i hi
          simp only [Finset.mem_range] at hi
          simp only [Finset.mem_Icc]
          omega
        · intro i hi j hj he
          omega
        · intro j hj
          simp only [Finset.mem_Icc] at hj
          refine ⟨j - m - 1, ?_, ?_⟩
          · simp only [Finset.mem_range]
            omega
          · omega
        · intro i hi
          have hi' : i ≤ n := by exact Finset.mem_range_succ_iff.mp hi
          have he1 : n - i + (m + i + 1) = n + 1 + m := by omega
          have he2 : i + (m + 1) = m + i + 1 := by omega
          have h1 : T (n + 1 + m) (m + i + 1) =
              (n + 1 + m + 1) * B P (m + i + 1) (n - i) (n - i) := by
            simpa only [he1] using ih (n - i) (by omega) (m + i + 1)
          have h2 : T (m + i + 1) (m + 1) =
              (m + i + 1 + 1) * B P (m + 1) i i := by
            simpa only [he2] using ih i (by omega) (m + 1)
          rw [h1, h2]
          ring
  intro m
  simpa only [Set.indicator_apply, Set.mem_Iic, Nat.le_refl, ↓reduceIte] using hb n m

end D5.S1.Recurrence.Algebraic.KurkovA107667WeightedBallot
