/- GID: D5/S1/Recurrence/MatharA097967
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharA097967
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal factorial sum in A097967 satisfies Mathar's recurrence at all natural indices at least five. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
namespace D5.S1.Recurrence.MatharA097967

def literal (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n,
    ((n.factorial : ℚ) * ((k.factorial : ℚ) + 1)) /
      ((k.factorial : ℚ) * ((n-k).factorial : ℚ))

def b (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (n.descFactorial (k+1) : ℚ)


private lemma term_split (n k : ℕ) (hk : k ≤ n) :
    ((n.factorial : ℚ) * ((k.factorial : ℚ) + 1)) /
      ((k.factorial : ℚ) * ((n-k).factorial : ℚ)) =
        (n.descFactorial k : ℚ) + (n.choose k : ℚ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    Nat.cast_choose ℚ hk]
  have h : (k.factorial : ℚ) ≠ 0 := by positivity
  have h' : ((n-k).factorial : ℚ) ≠ 0 := by positivity
  field_simp

private lemma b_step (n : ℕ) : b (n+1) = ((n : ℚ)+1) * (b n+1) := by
  simp only [b, Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [← Finset.mul_sum, Finset.sum_range_succ']
  simp

end D5.S1.Recurrence.MatharA097967

namespace D5.S1.Recurrence.MatharA097967

private lemma sum_shift (f : ℕ → ℚ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, f k) = ∑ k ∈ Finset.range n, f (k+1) := by
  have hs : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hs, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private lemma choose_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, (n.choose (k+1) : ℚ)) = (2:ℚ)^n - 1 := by
  have h : (∑ k ∈ Finset.range (n+1), (n.choose k : ℚ)) = (2:ℚ)^n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, Nat.cast_one] at h
  linarith

private lemma literal_formula (n : ℕ) : literal n = b n + (2:ℚ)^n - 1 := by
  unfold literal
  rw [sum_shift]
  calc
    _ = ∑ k ∈ Finset.range n,
        ((n.descFactorial (k+1) : ℚ) + (n.choose (k+1) : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply term_split
      have := Finset.mem_range.mp hk
      omega
    _ = b n + (2:ℚ)^n - 1 := by
      rw [Finset.sum_add_distrib, choose_sum]
      simp only [b]
      ring

private lemma recurrence_forward (m : ℕ) :
    literal (m+5) + (-((m+5:ℕ):ℚ)-6)*literal (m+4) +
      (6*((m+5:ℕ):ℚ)+7)*literal (m+3) +
      (-13*((m+5:ℕ):ℚ)+14)*literal (m+2) +
      4*(3*((m+5:ℕ):ℚ)-8)*literal (m+1) +
      4*(-((m+5:ℕ):ℚ)+4)*literal m = 0 := by
  simp only [literal_formula, b_step, pow_succ, Nat.cast_add, Nat.cast_ofNat]
  ring

def claim : Prop := ∀ n : ℕ, 5 ≤ n →
    literal n + (-(n:ℚ)-6)*literal (n-1) +
      (6*(n:ℚ)+7)*literal (n-2) +
      (-13*(n:ℚ)+14)*literal (n-3) +
      4*(3*(n:ℚ)-8)*literal (n-4) +
      4*(-(n:ℚ)+4)*literal (n-5) = 0

theorem result : claim := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using recurrence_forward m

end D5.S1.Recurrence.MatharA097967
