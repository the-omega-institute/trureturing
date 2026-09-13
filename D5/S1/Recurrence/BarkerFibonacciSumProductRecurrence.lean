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

private theorem no_large_product_sum (i j r s : ℕ)
    (hij : j ≤ i) (hr : 5 ≤ r) (hs : 5 ≤ s)
    (heq : Nat.fib i + Nat.fib j = Nat.fib r * Nat.fib s) : False := by
  let t := r + s - 2
  have ht : 8 ≤ t := by dsimp [t]; omega
  have hgap := product_gap r s hr hs
  have hlow : Nat.fib t + Nat.fib (t - 4) < Nat.fib i + Nat.fib j := by
    rw [heq]
    simpa only [show r + s - 2 = t by rfl,
      show r + s - 6 = t - 4 by dsimp [t]; omega] using hgap.1
  have hupp : Nat.fib i + Nat.fib j < Nat.fib t + Nat.fib (t - 3) := by
    rw [heq]
    simpa only [show r + s - 2 = t by rfl,
      show r + s - 5 = t - 3 by dsimp [t]; omega] using hgap.2
  have hf1 : Nat.fib (t - 1) = Nat.fib (t - 3) + Nat.fib (t - 2) := by
    simpa only [show t - 3 + 2 = t - 1 by omega,
      show t - 3 + 1 = t - 2 by omega] using
        (Nat.fib_add_two (n := t - 3))
  have hf2 : Nat.fib t = Nat.fib (t - 2) + Nat.fib (t - 1) := by
    simpa only [show t - 2 + 2 = t by omega,
      show t - 2 + 1 = t - 1 by omega] using
        (Nat.fib_add_two (n := t - 2))
  have hf3 : Nat.fib (t + 1) = Nat.fib (t - 1) + Nat.fib t := by
    simpa only [show t - 1 + 2 = t + 1 by omega,
      show t - 1 + 1 = t by omega] using
        (Nat.fib_add_two (n := t - 1))
  have hfsmall : Nat.fib (t - 2) < Nat.fib (t - 1) := by
    simpa only [show t - 2 + 1 = t - 1 by omega] using
      (Nat.fib_lt_fib_succ (n := t - 2) (by omega))
  have hflarge : Nat.fib (t - 3) < Nat.fib (t - 1) := by
    have h : Nat.fib (t - 3) < Nat.fib (t - 2) := by
      simpa only [show t - 3 + 1 = t - 2 by omega] using
        (Nat.fib_lt_fib_succ (n := t - 3) (by omega))
    exact lt_trans h hfsmall
  have hbound : Nat.fib t + Nat.fib (t - 3) =
      2 * Nat.fib (t - 1) := by omega
  have hi_lt : i < t + 1 := by
    by_contra h
    have hmono : Nat.fib (t + 1) ≤ Nat.fib i := Nat.fib_mono (by omega)
    omega
  have hi_ge : t - 2 < i := by
    by_contra h
    have hmonoI : Nat.fib i ≤ Nat.fib (t - 2) := Nat.fib_mono (by omega)
    have hmonoJ : Nat.fib j ≤ Nat.fib (t - 2) := Nat.fib_mono (by omega)
    omega
  by_cases hit : i = t
  · subst i
    have hjlow : Nat.fib (t - 4) < Nat.fib j := by omega
    have hjupp : Nat.fib j < Nat.fib (t - 3) := by omega
    have hjindexLow : t - 4 < j :=
      (Nat.fib_lt_fib (by omega : 2 ≤ t - 4)).mp hjlow
    have hjindexUpp : j < t - 3 :=
      (Nat.fib_lt_fib (by omega : 2 ≤ j)).mp hjupp
    omega
  · have hi1 : i = t - 1 := by omega
    subst i
    by_cases hj1 : j = t - 1
    · subst j
      omega
    · have hjle : Nat.fib j ≤ Nat.fib (t - 2) := Nat.fib_mono (by omega)
      omega

private theorem mem_iff_family (x : ℕ) :
    mem x ↔ ∃ k, x = Nat.fib k ∨ x = 2 * Nat.fib k ∨ x = 3 * Nat.fib k := by
  constructor
  · rintro ⟨⟨i, j, hsum⟩, ⟨r, s, hproduct⟩⟩
    have hsmall : r ≤ 4 ∨ s ≤ 4 := by
      by_contra hn
      push Not at hn
      have heq : Nat.fib i + Nat.fib j = Nat.fib r * Nat.fib s :=
        hsum.symm.trans hproduct
      rcases le_total j i with hji | hij
      · exact no_large_product_sum i j r s hji (by omega) (by omega) heq
      · exact no_large_product_sum j i r s hij (by omega) (by omega)
          (by simpa only [add_comm] using heq)
    have small_factor (u v : ℕ) (hu : u ≤ 4)
        (h : x = Nat.fib u * Nat.fib v) :
        ∃ k, x = Nat.fib k ∨ x = 2 * Nat.fib k ∨ x = 3 * Nat.fib k := by
      interval_cases u
      · exact ⟨0, Or.inl (by simpa using h)⟩
      · exact ⟨v, Or.inl (by simpa using h)⟩
      · exact ⟨v, Or.inl (by simpa using h)⟩
      · exact ⟨v, Or.inr (Or.inl (by simpa [show Nat.fib 3 = 2 by decide] using h))⟩
      · exact ⟨v, Or.inr (Or.inr (by simpa [show Nat.fib 4 = 3 by decide] using h))⟩
    rcases hsmall with hr | hs
    · exact small_factor r s hr hproduct
    · exact small_factor s r hs (by simpa only [mul_comm] using hproduct)
  · rintro ⟨k, hk | hk | hk⟩
    · refine ⟨⟨k, 0, ?_⟩, ⟨k, 1, ?_⟩⟩
      · simpa only [Nat.fib_zero, add_zero] using hk
      · simpa only [Nat.fib_one, mul_one] using hk
    · refine ⟨⟨k, k, ?_⟩, ⟨3, k, ?_⟩⟩
      · simpa only [two_mul] using hk
      · simpa only [show Nat.fib 3 = 2 by decide] using hk
    · by_cases hzero : k = 0
      · subst k
        have hx : x = 0 := by simpa using hk
        subst x
        exact ⟨⟨0, 0, by decide⟩, ⟨0, 0, by decide⟩⟩
      by_cases hone : k = 1
      · subst k
        have hx : x = 3 := by simpa using hk
        subst x
        exact ⟨⟨1, 3, by decide⟩, ⟨4, 1, by decide⟩⟩
      have hk2 : 2 ≤ k := by omega
      have h1 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) :=
        Nat.fib_add_two
      have h2 : Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k := by
        simpa only [show k - 1 + 2 = k + 1 by omega,
          show k - 1 + 1 = k by omega] using
            (Nat.fib_add_two (n := k - 1))
      have h3 : Nat.fib k = Nat.fib (k - 2) + Nat.fib (k - 1) := by
        simpa only [show k - 2 + 2 = k by omega,
          show k - 2 + 1 = k - 1 by omega] using
            (Nat.fib_add_two (n := k - 2))
      have hsum : Nat.fib (k + 2) + Nat.fib (k - 2) = 3 * Nat.fib k := by omega
      refine ⟨⟨k + 2, k - 2, ?_⟩, ⟨4, k, ?_⟩⟩
      · exact hk.trans hsum.symm
      · simpa only [show Nat.fib 4 = 3 by decide] using hk

private theorem family_interleave (k : ℕ) (hk : 4 ≤ k) :
    2 * Nat.fib k < Nat.fib (k + 2) ∧
      Nat.fib (k + 2) < 3 * Nat.fib k ∧
        3 * Nat.fib k < 2 * Nat.fib (k + 1) ∧
          2 * Nat.fib (k + 1) < Nat.fib (k + 3) := by
  have hprev : Nat.fib (k - 2) < Nat.fib (k - 1) := by
    simpa only [show k - 2 + 1 = k - 1 by omega] using
      (Nat.fib_lt_fib_succ (n := k - 2) (by omega))
  have hcur : Nat.fib (k - 1) < Nat.fib k := by
    simpa only [show k - 1 + 1 = k by omega] using
      (Nat.fib_lt_fib_succ (n := k - 1) (by omega))
  have hnext : Nat.fib k < Nat.fib (k + 1) :=
    Nat.fib_lt_fib_succ (by omega)
  have hnext2 : Nat.fib (k + 1) < Nat.fib (k + 2) :=
    Nat.fib_lt_fib_succ (by omega)
  have hf0 : Nat.fib k = Nat.fib (k - 2) + Nat.fib (k - 1) := by
    simpa only [show k - 2 + 2 = k by omega,
      show k - 2 + 1 = k - 1 by omega] using
        (Nat.fib_add_two (n := k - 2))
  have hf1 : Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k := by
    simpa only [show k - 1 + 2 = k + 1 by omega,
      show k - 1 + 1 = k by omega] using
        (Nat.fib_add_two (n := k - 1))
  have hf2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) :=
    Nat.fib_add_two
  have hf3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
    simpa only [show k + 1 + 2 = k + 3 by omega] using
      (Nat.fib_add_two (n := k + 1))
  omega

end D5.S1.Recurrence.BarkerFibonacciSumProductRecurrence
