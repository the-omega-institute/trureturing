/- GID: D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/BarkerFibonacciSumProductRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.Data.Nat.Nth, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: none
   digest: Barker's Fibonacci sum-product sequence obeys a three-and-six-step recurrence. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.IntervalCases

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

private def candidate (n : ℕ) : ℕ :=
  if n < 6 then n
  else if n % 3 = 0 then 2 * Nat.fib (n / 3 + 2)
  else if n % 3 = 1 then Nat.fib (n / 3 + 4)
  else 3 * Nat.fib (n / 3 + 2)

private theorem candidate_eq_nth (n : ℕ) : candidate n = Nat.nth mem n := by
  have family_interleave (k : ℕ) (hk : 4 ≤ k) :
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
  have candidate_zero (m : ℕ) :
      candidate (3 * m + 6) = 2 * Nat.fib (m + 4) := by
    simp only [candidate, if_neg (show ¬ 3 * m + 6 < 6 by omega),
      if_pos (show (3 * m + 6) % 3 = 0 by omega),
      show (3 * m + 6) / 3 + 2 = m + 4 by omega]
  have candidate_one (m : ℕ) :
      candidate (3 * m + 7) = Nat.fib (m + 6) := by
    simp only [candidate, if_neg (show ¬ 3 * m + 7 < 6 by omega),
      if_neg (show (3 * m + 7) % 3 ≠ 0 by omega),
      if_pos (show (3 * m + 7) % 3 = 1 by omega),
      show (3 * m + 7) / 3 + 4 = m + 6 by omega]
  have candidate_two (m : ℕ) :
      candidate (3 * m + 8) = 3 * Nat.fib (m + 4) := by
    simp only [candidate, if_neg (show ¬ 3 * m + 8 < 6 by omega),
      if_neg (show (3 * m + 8) % 3 ≠ 0 by omega),
      if_neg (show (3 * m + 8) % 3 ≠ 1 by omega),
      show (3 * m + 8) / 3 + 2 = m + 4 by omega]
  have candidate_strictMono : StrictMono candidate := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    by_cases hi : i < 5
    · have hi' : i + 1 < 6 := by omega
      simp only [candidate, if_pos (by omega : i < 6), if_pos hi']
      omega
    by_cases hi5 : i = 5
    · subst i
      decide
    have hi6 : 6 ≤ i := by omega
    let m := (i - 6) / 3
    let rem := (i - 6) % 3
    have hrem : rem < 3 := Nat.mod_lt _ (by decide)
    have hdecomp : i = 3 * m + 6 + rem := by dsimp [m, rem]; omega
    rcases (by omega : rem = 0 ∨ rem = 1 ∨ rem = 2) with hr | hr | hr
    · rw [hdecomp, hr]
      simpa only [add_zero, show 3 * m + 6 + 1 = 3 * m + 7 by omega,
        candidate_zero, candidate_one] using
        (family_interleave (m + 4) (by omega)).1
    · rw [hdecomp, hr]
      simpa only [show 3 * m + 6 + 1 = 3 * m + 7 by omega,
        show 3 * m + 6 + 1 + 1 = 3 * m + 8 by omega,
        candidate_one, candidate_two] using
        (family_interleave (m + 4) (by omega)).2.1
    · rw [hdecomp, hr]
      have h := (family_interleave (m + 4) (by omega)).2.2.1
      simpa only [show 3 * m + 6 + 2 = 3 * m + 8 by omega,
        candidate_two, candidate_zero,
        show 3 * m + 8 + 1 = 3 * (m + 1) + 6 by omega,
        show m + 4 + 1 = m + 1 + 4 by omega] using h
  have hmaps (i : ℕ) : mem (candidate i) := by
    apply (mem_iff_family _).2
    by_cases hi : i < 6
    · interval_cases i
      · exact ⟨0, Or.inl (by decide)⟩
      · exact ⟨1, Or.inl (by decide)⟩
      · exact ⟨3, Or.inl (by decide)⟩
      · exact ⟨4, Or.inl (by decide)⟩
      · exact ⟨3, Or.inr (Or.inl (by decide))⟩
      · exact ⟨5, Or.inl (by decide)⟩
    · let m := (i - 6) / 3
      let rem := (i - 6) % 3
      have hrem : rem < 3 := Nat.mod_lt _ (by decide)
      have hdecomp : i = 3 * m + 6 + rem := by dsimp [m, rem]; omega
      rcases (by omega : rem = 0 ∨ rem = 1 ∨ rem = 2) with hr | hr | hr
      · refine ⟨m + 4, Or.inr (Or.inl ?_)⟩
        rw [hdecomp, hr, add_zero, candidate_zero]
      · refine ⟨m + 6, Or.inl ?_⟩
        rw [hdecomp, hr, show 3 * m + 6 + 1 = 3 * m + 7 by omega,
          candidate_one]
      · refine ⟨m + 4, Or.inr (Or.inr ?_)⟩
        rw [hdecomp, hr, show 3 * m + 6 + 2 = 3 * m + 8 by omega,
          candidate_two]
  have hsurj (x : ℕ) (hx : mem x) : ∃ i, candidate i = x := by
    rcases (mem_iff_family x).1 hx with ⟨k, hf | hf | hf⟩
    · by_cases hk : k < 6
      · interval_cases k
        · exact ⟨0, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨1, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨1, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨2, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨3, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨5, by simpa [candidate, Nat.fib] using hf.symm⟩
      · refine ⟨3 * (k - 6) + 7, ?_⟩
        simpa only [candidate_one, show k - 6 + 6 = k by omega] using hf.symm
    · by_cases hk : k < 4
      · interval_cases k
        · exact ⟨0, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨2, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨2, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨4, by simpa [candidate, Nat.fib] using hf.symm⟩
      · refine ⟨3 * (k - 4) + 6, ?_⟩
        simpa only [candidate_zero, show k - 4 + 4 = k by omega] using hf.symm
    · by_cases hk : k < 4
      · interval_cases k
        · exact ⟨0, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨3, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨3, by simpa [candidate, Nat.fib] using hf.symm⟩
        · exact ⟨6, by simpa [candidate, Nat.fib] using hf.symm⟩
      · refine ⟨3 * (k - 4) + 8, ?_⟩
        simpa only [candidate_two, show k - 4 + 4 = k by omega] using hf.symm
  have hinfinite : (Set.ofPred mem).Infinite := by
    apply (Set.infinite_range_of_injective candidate_strictMono.injective).mono
    rintro x ⟨i, rfl⟩
    exact hmaps i
  have hfull : ∀ hf : (Set.ofPred mem).Finite, n < hf.toFinset.card := by
    intro hf
    exact (hinfinite hf).elim
  exact Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn candidate
    (by
      intro x hx
      rcases hsurj x hx with ⟨i, rfl⟩
      exact ⟨i, by intro hf; exact (hinfinite hf).elim, rfl⟩)
    (by intro i hi; exact hmaps i)
    (candidate_strictMono.strictMonoOn _) hfull

theorem barker_a226857 : ∀ n : ℕ, 12 < n → a n = a (n - 3) + a (n - 6) := by
  intro n hn
  have candidate_zero (m : ℕ) :
      candidate (3 * m + 6) = 2 * Nat.fib (m + 4) := by
    simp only [candidate, if_neg (show ¬ 3 * m + 6 < 6 by omega),
      if_pos (show (3 * m + 6) % 3 = 0 by omega),
      show (3 * m + 6) / 3 + 2 = m + 4 by omega]
  have candidate_one (m : ℕ) :
      candidate (3 * m + 7) = Nat.fib (m + 6) := by
    simp only [candidate, if_neg (show ¬ 3 * m + 7 < 6 by omega),
      if_neg (show (3 * m + 7) % 3 ≠ 0 by omega),
      if_pos (show (3 * m + 7) % 3 = 1 by omega),
      show (3 * m + 7) / 3 + 4 = m + 6 by omega]
  have candidate_two (m : ℕ) :
      candidate (3 * m + 8) = 3 * Nat.fib (m + 4) := by
    simp only [candidate, if_neg (show ¬ 3 * m + 8 < 6 by omega),
      if_neg (show (3 * m + 8) % 3 ≠ 0 by omega),
      if_neg (show (3 * m + 8) % 3 ≠ 1 by omega),
      show (3 * m + 8) / 3 + 2 = m + 4 by omega]
  simp only [a, ← candidate_eq_nth]
  let p := n - 1
  let m := (p - 6) / 3
  let rem := (p - 6) % 3
  have hm : 2 ≤ m := by dsimp [m, p]; omega
  have hrem : rem < 3 := Nat.mod_lt _ (by decide)
  have hp : p = 3 * m + 6 + rem := by dsimp [p, m, rem]; omega
  have hsub3 : n - 3 - 1 = p - 3 := by dsimp [p]; omega
  have hsub6 : n - 6 - 1 = p - 6 := by dsimp [p]; omega
  change candidate p = candidate (n - 3 - 1) + candidate (n - 6 - 1)
  rw [hsub3, hsub6]
  rcases (by omega : rem = 0 ∨ rem = 1 ∨ rem = 2) with hr | hr | hr
  · rw [hp, hr, add_zero,
      show 3 * m + 6 - 3 = 3 * (m - 1) + 6 by omega,
      show 3 * m + 6 - 6 = 3 * (m - 2) + 6 by omega,
      candidate_zero, candidate_zero, candidate_zero]
    have h : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
      simpa only [show m + 2 + 2 = m + 4 by omega,
        show m + 2 + 1 = m + 3 by omega] using
          (Nat.fib_add_two (n := m + 2))
    have hm1 : m - 1 + 4 = m + 3 := by omega
    have hm2 : m - 2 + 4 = m + 2 := by omega
    rw [hm1, hm2]
    omega
  · rw [hp, hr,
      show 3 * m + 6 + 1 = 3 * m + 7 by omega,
      show 3 * m + 7 - 3 = 3 * (m - 1) + 7 by omega,
      show 3 * m + 7 - 6 = 3 * (m - 2) + 7 by omega,
      candidate_one, candidate_one, candidate_one]
    have h : Nat.fib (m + 6) = Nat.fib (m + 4) + Nat.fib (m + 5) := by
      simpa only [show m + 4 + 2 = m + 6 by omega,
        show m + 4 + 1 = m + 5 by omega] using
          (Nat.fib_add_two (n := m + 4))
    have hm1 : m - 1 + 6 = m + 5 := by omega
    have hm2 : m - 2 + 6 = m + 4 := by omega
    rw [hm1, hm2]
    omega
  · rw [hp, hr,
      show 3 * m + 6 + 2 = 3 * m + 8 by omega,
      show 3 * m + 8 - 3 = 3 * (m - 1) + 8 by omega,
      show 3 * m + 8 - 6 = 3 * (m - 2) + 8 by omega,
      candidate_two, candidate_two, candidate_two]
    have h : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
      simpa only [show m + 2 + 2 = m + 4 by omega,
        show m + 2 + 1 = m + 3 by omega] using
          (Nat.fib_add_two (n := m + 2))
    have hm1 : m - 1 + 4 = m + 3 := by omega
    have hm2 : m - 2 + 4 = m + 2 := by omega
    rw [hm1, hm2]
    omega

#print axioms barker_a226857

end D5.S1.Recurrence.BarkerFibonacciSumProductRecurrence
