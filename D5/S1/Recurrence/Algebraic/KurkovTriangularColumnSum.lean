/- GID: D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/KurkovTriangularColumnSum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Every lawful A396981 array satisfies Kurkov's positive-column factorial sum. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The source is Mikhail Kurkov's Conjecture 1 in OEIS A396981, with the
positive-index A002024 convention. OEIS Foundation, CC-BY-SA 4.0.
Pinned source: oeis/oeisdata d4ade8b4ca7c6ff0ac8931532918fd4f6176805e,
seq/A396/A396981.seq and seq/A002/A002024.seq.
Only the defining array equations are hypotheses. The value of `f 0` is an
auxiliary totalization and is never used by a positive-column source clause.
-/

open Finset

namespace D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum

private theorem upper_exists (q : ℕ) : ∃ s : ℕ, 2 * q ≤ s * (s + 1) := by
  refine ⟨2 * q, ?_⟩
  nlinarith

/-- A002024 at positive indices, totalized at zero solely for Lean's function type. -/
def f (q : ℕ) : ℕ := Nat.find (upper_exists q)

private theorem f_upper (q : ℕ) : 2 * q ≤ f q * (f q + 1) :=
  Nat.find_spec (upper_exists q)

private theorem f_pos {q : ℕ} (hq : 0 < q) : 0 < f q := by
  have h := f_upper q
  by_contra hn
  have hz : f q = 0 := by omega
  rw [hz] at h
  omega

private theorem f_lower {q : ℕ} (hq : 0 < q) : f q * (f q - 1) < 2 * q := by
  have hp := f_pos hq
  have h := Nat.find_min (upper_exists q) (show f q - 1 < f q by omega)
  change ¬ 2 * q ≤ (f q - 1) * (f q - 1 + 1) at h
  have he : f q - 1 + 1 = f q := by omega
  rw [he] at h
  nlinarith

private theorem f_characterization {q s : ℕ} (hq : 0 < q) :
    f q = s ↔ 1 ≤ s ∧ s * (s - 1) / 2 < q ∧ q ≤ s * (s + 1) / 2 := by
  constructor
  · rintro rfl
    refine ⟨f_pos hq, ?_, ?_⟩
    · have h := f_lower hq
      omega
    · have h := f_upper q
      omega
  · rintro ⟨hs, hlo, hhi⟩
    apply (Nat.find_eq_iff (upper_exists q)).2
    constructor
    · omega
    · intro t ht hbad
      have hts : t ≤ s - 1 := by omega
      have hm := Nat.mul_le_mul hts (show t + 1 ≤ s by omega)
      have hl : s * (s - 1) < 2 * q := by omega
      nlinarith

private theorem f_shift {k : ℕ} (hk : 0 < k) : f (k + f k + 1) = f k + 1 := by
  apply (f_characterization (q := k + f k + 1) (by omega)).2
  have hu := f_upper k
  have hl := f_lower hk
  have hp := f_pos hk
  have he : f k - 1 + 1 = f k := by omega
  refine ⟨by omega, ?_, ?_⟩
  · have h : (f k + 1) * (f k + 1 - 1) < 2 * (k + f k + 1) := by
      have he' : f k + 1 - 1 = f k := by omega
      rw [he']
      nlinarith
    omega
  · have h : 2 * (k + f k + 1) ≤ (f k + 1) * (f k + 1 + 1) := by
      nlinarith
    omega

/-- All original natural-valued array equations, with the positive-domain guards. -/
def IsArray (A : ℕ → ℕ → ℕ) : Prop :=
  (∀ q, A 0 q = 1) ∧
  (∀ n, 1 ≤ n → A n 0 = 0) ∧
  ∀ n q, 1 ≤ n → 1 ≤ q →
    A n q = A n (q - f q) + (n + f q - 1) * A (n - 1) q

private def array : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n + 1, q + 1 => array (n + 1) (q + 1 - f (q + 1)) +
      (n + f (q + 1)) * array n (q + 1)
termination_by n q => (n, q)
decreasing_by
  · apply Prod.Lex.right
    exact Nat.sub_lt (Nat.succ_pos _) (f_pos (Nat.succ_pos _))
  · apply Prod.Lex.left
    omega

private theorem array_lawful : IsArray array := by
  refine ⟨?_, ?_, ?_⟩
  · intro q; rw [array]
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [array]
  · intro n q hn hq
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    simp only [Nat.succ_eq_add_one]
    rw [array]
    congr 1
    congr 1
    omega

private theorem column_step (A : ℕ → ℕ → ℕ) (hA : IsArray A)
    (n k : ℕ) (hk : 1 ≤ k) :
    A (n + 1) (k + f k + 1) = A (n + 1) k +
      (n + 1 + f k) * A n (k + f k + 1) := by
  have h := hA.2.2 (n + 1) (k + f k + 1) (by omega) (by omega)
  rw [f_shift hk] at h
  simpa only [show k + f k + 1 - (f k + 1) = k by omega,
    show n + 1 + (f k + 1) - 1 = n + 1 + f k by omega,
    Nat.add_sub_cancel] using h

private theorem factorial_ne_zero (m : ℕ) : (m.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero m

private theorem column_sum (A : ℕ → ℕ → ℕ) (hA : IsArray A)
    (n k : ℕ) (hk : 1 ≤ k) :
    (A n (k + f k + 1) : ℚ) =
      ∑ j ∈ range (n + 1), (A j k : ℚ) *
        ((n + f k).factorial : ℚ) / ((f k + j).factorial : ℚ) := by
  induction n with
  | zero =>
    simp only [sum_range_one, hA.1, Nat.cast_one, Nat.zero_add, Nat.add_zero, one_mul]
    exact (div_self (factorial_ne_zero (f k))).symm
  | succ n ih =>
    rw [column_step A hA n k hk]
    push_cast
    rw [ih]
    conv_rhs => rw [sum_range_succ]
    have hfac : ((n + 1 + f k).factorial : ℚ) =
        (n + 1 + f k : ℚ) * ((n + f k).factorial : ℚ) := by
      rw [show n + 1 + f k = (n + f k) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    have hs : (∑ j ∈ range (n + 1), (A j k : ℚ) *
        ((n + 1 + f k : ℚ) * ((n + f k).factorial : ℚ)) /
          ((f k + j).factorial : ℚ)) =
        (n + 1 + f k : ℚ) *
        ∑ j ∈ range (n + 1), (A j k : ℚ) *
          ((n + f k).factorial : ℚ) / ((f k + j).factorial : ℚ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    rw [hs]
    have he : f k + (n + 1) = n + 1 + f k := by omega
    rw [he, hfac]
    have hz : (n + 1 + f k : ℚ) * ((n + f k).factorial : ℚ) ≠ 0 := by
      rw [← hfac]
      exact factorial_ne_zero _
    rw [mul_div_cancel_right₀ _ hz]
    ring

/-- The complete positive-column source event, including a lawful array's existence. -/
theorem result :
    (∃ A : ℕ → ℕ → ℕ, IsArray A) ∧
    ∀ A : ℕ → ℕ → ℕ, IsArray A → ∀ n k : ℕ, 1 ≤ k →
      (A n (k + f k + 1) : ℚ) =
        ∑ j ∈ range (n + 1), (A j k : ℚ) *
          ((n + f k).factorial : ℚ) / ((f k + j).factorial : ℚ) := by
  exact ⟨⟨array, array_lawful⟩, column_sum⟩

end D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum
