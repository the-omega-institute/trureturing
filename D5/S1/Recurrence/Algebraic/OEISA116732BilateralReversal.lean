/- GID: D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/OEISA116732BilateralReversal
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: The bilateral A116732 companion has a unique solution, and u_n = -u_(2-n). -/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The unrounded A116732 companion extended to all integer indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Algebraic.OEISA116732BilateralReversal

/-- The bilateral recurrence u_n = u_{n-1} + u_{n-2} + u_{n-3} - u_{n-4} on all integers. -/
def IsRec (u : ℤ → ℤ) : Prop := ∀ n : ℤ, u n = u (n - 1) + u (n - 2) + u (n - 3) - u (n - 4)

/-- The initial values u_0 = u_1 = u_2 = 0 and u_3 = 1. -/
def IsInit (u : ℤ → ℤ) : Prop := u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0 ∧ u 3 = 1

private theorem zero_of_rec (d : ℤ → ℤ) (hd : IsRec d) (h0 : d 0 = 0) (h1 : d 1 = 0)
    (h2 : d 2 = 0) (h3 : d 3 = 0) : ∀ n, d n = 0 := by
  have fwd : ∀ k : ℕ, d k = 0 ∧ d (k + 1) = 0 ∧ d (k + 2) = 0 ∧ d (k + 3) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨h0, h1, h2, h3⟩
    | succ k ih =>
      obtain ⟨a, b, c, e⟩ := ih
      have := hd ((k : ℤ) + 4)
      push_cast
      refine ⟨by simpa using b, by rw [show (k : ℤ) + 1 + 1 = k + 2 by ring]; exact c,
        by rw [show (k : ℤ) + 1 + 2 = k + 3 by ring]; exact e, ?_⟩
      rw [show (k : ℤ) + 1 + 3 = k + 4 by ring, this]
      simp only [show (k : ℤ) + 4 - 1 = k + 3 by ring, show (k : ℤ) + 4 - 2 = k + 2 by ring,
        show (k : ℤ) + 4 - 3 = k + 1 by ring, show (k : ℤ) + 4 - 4 = k by ring, a, b, c, e]
      norm_num
  have bwd : ∀ k : ℕ, d (-k) = 0 ∧ d (-k + 1) = 0 ∧ d (-k + 2) = 0 ∧ d (-k + 3) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨h0, h1, h2, h3⟩
    | succ k ih =>
      obtain ⟨a, b, c, e⟩ := ih
      have := hd (-(k : ℤ) + 3)
      push_cast
      refine ⟨?_, by rw [show -((k : ℤ) + 1) + 1 = -k by ring]; exact a,
        by rw [show -((k : ℤ) + 1) + 2 = -k + 1 by ring]; exact b,
        by rw [show -((k : ℤ) + 1) + 3 = -k + 2 by ring]; exact c⟩
      rw [show -(k : ℤ) + 3 - 1 = -k + 2 by ring, show -(k : ℤ) + 3 - 2 = -k + 1 by ring,
        show -(k : ℤ) + 3 - 3 = -k by ring, show -(k : ℤ) + 3 - 4 = -((k : ℤ) + 1) by ring,
        a, b, c, e] at this
      linarith
  intro n
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact (fwd k).1
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -k := ⟨(-n).toNat, by omega⟩
    rw [hk]; exact (bwd k).1

/-- Forward values on the natural numbers. -/
private def w : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 => w (n + 3) + w (n + 2) + w (n + 1) - w n

/-- The bilateral extension, reflected through index one. -/
private def u (n : ℤ) : ℤ := if 0 ≤ n then w n.toNat else -w (2 - n).toNat

private theorem w_rec (m : ℕ) : w (m + 4) = w (m + 3) + w (m + 2) + w (m + 1) - w m := rfl

private theorem u_rec : IsRec u := by
  intro n
  rcases le_or_gt 4 n with hn | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 4 := ⟨(n - 4).toNat, by omega⟩
    simp only [u, show (0 : ℤ) ≤ m + 4 by omega, show (0 : ℤ) ≤ m + 4 - 1 by omega,
      show (0 : ℤ) ≤ m + 4 - 2 by omega, show (0 : ℤ) ≤ m + 4 - 3 by omega,
      show (0 : ℤ) ≤ m + 4 - 4 by omega, ite_true]
    rw [show ((m : ℤ) + 4).toNat = m + 4 by omega, show ((m : ℤ) + 4 - 1).toNat = m + 3 by omega,
      show ((m : ℤ) + 4 - 2).toNat = m + 2 by omega, show ((m : ℤ) + 4 - 3).toNat = m + 1 by omega,
      show ((m : ℤ) + 4 - 4).toNat = m by omega, w_rec]
  rcases lt_or_ge n 0 with hn' | hn'
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    simp only [u, show ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 by omega,
      show ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 - 1 by omega,
      show ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 - 2 by omega, show ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 - 3 by omega,
      show ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 - 4 by omega, ite_false]
    rw [show (2 - (-(m : ℤ) - 1)).toNat = m + 3 by omega,
      show (2 - (-(m : ℤ) - 1 - 1)).toNat = m + 4 by omega,
      show (2 - (-(m : ℤ) - 1 - 2)).toNat = m + 5 by omega,
      show (2 - (-(m : ℤ) - 1 - 3)).toNat = m + 6 by omega,
      show (2 - (-(m : ℤ) - 1 - 4)).toNat = m + 7 by omega]
    have h7 := w_rec (m + 3)
    simp only [show m + 3 + 4 = m + 7 by ring, show m + 3 + 3 = m + 6 by ring,
      show m + 3 + 2 = m + 5 by ring, show m + 3 + 1 = m + 4 by ring] at h7
    linarith
  · have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide

private theorem u_init : IsInit u := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

private theorem reversal (v : ℤ → ℤ) (hr : IsRec v) (hi : IsInit v) : ∀ n, v n = -v (2 - n) := by
  obtain ⟨i0, i1, i2, i3⟩ := hi
  have hm1 : v (-1) = -1 := by have := hr 3; norm_num at this; linarith
  have key := zero_of_rec (fun n => v n + v (2 - n)) (by
      intro n
      have a := hr n
      have b := hr (6 - n)
      simp only [show (6 : ℤ) - n - 1 = 5 - n by ring, show (6 : ℤ) - n - 2 = 4 - n by ring,
        show (6 : ℤ) - n - 3 = 3 - n by ring, show (6 : ℤ) - n - 4 = 2 - n by ring] at b
      simp only [show (2 : ℤ) - (n - 1) = 3 - n by ring, show (2 : ℤ) - (n - 2) = 4 - n by ring,
        show (2 : ℤ) - (n - 3) = 5 - n by ring, show (2 : ℤ) - (n - 4) = 6 - n by ring]
      linarith)
    (by simp [i0, i2]) (by norm_num [i1]) (by simp [i0, i2]) (by norm_num [i3, hm1])
  intro n
  have := key n
  linarith

/-- The initial values and the bilateral recurrence determine a unique integer sequence, and every
such sequence satisfies Somos's reversal identity `u n = -u (2 - n)`. -/
theorem result :
    (∃! u : ℤ → ℤ, IsInit u ∧ IsRec u) ∧
      ∀ u : ℤ → ℤ, IsInit u → IsRec u → ∀ n, u n = -u (2 - n) := by
  refine ⟨⟨u, ⟨u_init, u_rec⟩, ?_⟩, fun v hi hr => reversal v hr hi⟩
  rintro v ⟨hi, hr⟩
  funext n
  obtain ⟨a0, a1, a2, a3⟩ := hi
  obtain ⟨b0, b1, b2, b3⟩ := u_init
  have := zero_of_rec (fun n => v n - u n)
    (by intro n; have := hr n; have := u_rec n; simp only; linarith)
    (by simp [a0, b0]) (by simp [a1, b1]) (by simp [a2, b2]) (by simp [a3, b3]) n
  linarith

end D5.S1.Recurrence.Algebraic.OEISA116732BilateralReversal
