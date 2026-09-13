/- GID: D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/BarkerFibonacciSumProductRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.Data.Nat.Nth, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Two-step induction bounds products of large Fibonacci numbers. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

namespace D5.S1.Recurrence.BarkerFibonacciSumProductRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

def mem (x : ℕ) : Prop :=
  (∃ i j : ℕ, x = Nat.fib i + Nat.fib j) ∧
    (∃ r s : ℕ, x = Nat.fib r * Nat.fib s)

noncomputable def a (n : ℕ) : ℕ := Nat.nth mem (n - 1)

private theorem product_gap (r s : ℕ) (hr : 5 ≤ r) (hs : 5 ≤ s) :
    Nat.fib (r + s - 2) + Nat.fib (r + s - 6) < Nat.fib r * Nat.fib s ∧
      Nat.fib r * Nat.fib s <
        Nat.fib (r + s - 2) + Nat.fib (r + s - 5) := by
  let L (i j : ℕ) := Nat.fib (i + j + 8) + Nat.fib (i + j + 4)
  let P (i j : ℕ) := Nat.fib (i + 5) * Nat.fib (j + 5)
  let U (i j : ℕ) := Nat.fib (i + j + 8) + Nat.fib (i + j + 5)
  have fib_step (i j k : ℕ) :
      Nat.fib (i + 2 + j + k) =
        Nat.fib (i + j + k) + Nat.fib (i + 1 + j + k) := by
    rw [show i + 2 + j + k = (i + j + k) + 2 by omega, Nat.fib_add_two]
    rw [show i + 1 + j + k = i + j + k + 1 by omega]
  have hL (i j : ℕ) : L (i + 2) j = L i j + L (i + 1) j := by
    dsimp [L]
    rw [fib_step i j 8, fib_step i j 4]
    omega
  have hU (i j : ℕ) : U (i + 2) j = U i j + U (i + 1) j := by
    dsimp [U]
    rw [fib_step i j 8, fib_step i j 5]
    omega
  have hP (i j : ℕ) : P (i + 2) j = P i j + P (i + 1) j := by
    dsimp [P]
    rw [show i + 2 + 5 = (i + 5) + 2 by omega, Nat.fib_add_two]
    convert Nat.add_mul (Nat.fib (i + 5)) (Nat.fib (i + 5 + 1)) (Nat.fib (j + 5)) using 1
  have hLsym (i j : ℕ) : L i j = L j i := by
    simp only [L, show j + i = i + j by omega]
  have hPsym (i j : ℕ) : P i j = P j i := by
    simp only [P]
    exact mul_comm _ _
  have hUsym (i j : ℕ) : U i j = U j i := by
    simp only [U, show j + i = i + j by omega]
  have hLrow (i j : ℕ) : L i (j + 2) = L i j + L i (j + 1) := by
    calc
      L i (j + 2) = L (j + 2) i := hLsym _ _
      _ = L j i + L (j + 1) i := hL j i
      _ = L i j + L i (j + 1) := by rw [hLsym j i, hLsym (j + 1) i]
  have hProw (i j : ℕ) : P i (j + 2) = P i j + P i (j + 1) := by
    calc
      P i (j + 2) = P (j + 2) i := hPsym _ _
      _ = P j i + P (j + 1) i := hP j i
      _ = P i j + P i (j + 1) := by rw [hPsym j i, hPsym (j + 1) i]
  have hUrow (i j : ℕ) : U i (j + 2) = U i j + U i (j + 1) := by
    calc
      U i (j + 2) = U (j + 2) i := hUsym _ _
      _ = U j i + U (j + 1) i := hU j i
      _ = U i j + U i (j + 1) := by rw [hUsym j i, hUsym (j + 1) i]
  have base (i : ℕ) (hi : i = 0 ∨ i = 1) :
      ∀ j, L i j < P i j ∧ P i j < U i j := by
    rcases hi with rfl | rfl
    · intro j
      induction j using Nat.twoStepInduction with
      | zero => decide
      | one => decide
      | more j hj hj1 =>
        rw [hLrow, hProw, hUrow]
        omega
    · intro j
      induction j using Nat.twoStepInduction with
      | zero => decide
      | one => decide
      | more j hj hj1 =>
        rw [hLrow, hProw, hUrow]
        omega
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 5 := ⟨r - 5, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 5 := ⟨s - 5, by omega⟩
  have result : ∀ i j, L i j < P i j ∧ P i j < U i j := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero => exact base 0 (Or.inl rfl)
    | one => exact base 1 (Or.inr rfl)
    | more i hi hi1 =>
      intro j
      have h := hi j
      have h1 := hi1 j
      rw [hL i j, hP i j, hU i j]
      omega
  have h := result i j
  simpa only [L, P, U,
    show i + 5 + (j + 5) - 2 = i + j + 8 by omega,
    show i + 5 + (j + 5) - 6 = i + j + 4 by omega,
    show i + 5 + (j + 5) - 5 = i + j + 5 by omega] using h

end D5.S1.Recurrence.BarkerFibonacciSumProductRecurrence
