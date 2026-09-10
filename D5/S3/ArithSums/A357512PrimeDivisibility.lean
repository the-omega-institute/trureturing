/- GID: D5/S3/ArithSums/A357512PrimeDivisibility
   generality: G
   mirror-B: D5/B/S3/ArithSums/A357512PrimeDivisibility
   mirror-E: none(waiver:universal-divisibility-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: The fifth-weighted Apéry binomial sum at p-1 is divisible by p^4 for every prime p at least 5. -/

import D5.S1.Phase.Interference.DedekindReciprocityFiniteSums
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

open Finset

namespace D5.S3.ArithSums.A357512PrimeDivisibility

/-- OEIS A357512, with offset zero. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), k ^ 5 * (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

private def b (p k : ℕ) : ℕ := (p - 1).choose k * (p + k - 1).choose k

private lemma b_step (p k : ℕ) (hp : 0 < p) :
    (k + 1) ^ 2 * b p (k + 1) = (p - 1 - k) * (p + k) * b p k := by
  have h₁ := Nat.choose_succ_right_eq (p - 1) k
  have h₂ := Nat.add_one_mul_choose_eq (p + k - 1) k
  rw [show p + k - 1 + 1 = p + k by omega] at h₂
  dsimp [b]
  calc
    _ = ((p - 1).choose (k + 1) * (k + 1)) *
        ((p + k).choose (k + 1) * (k + 1)) := by ring
    _ = _ := by rw [h₁, ← h₂]; ring

private lemma transport {R : Type*} [CommRing R] (t x : R) (ht : t ^ 4 = 0) :
    ((t - x - 1) * (t + x)) ^ 2 * (t ^ 2 * x ^ 2 - 2 * t ^ 3 * x) =
      x ^ 4 * (t ^ 2 * (x + 1) ^ 2 - 2 * t ^ 3 * (x + 1)) := by
  linear_combination
    (-2*t^3*x + t^2*x^2 + 4*t^2*x + 4*t*x^3 + 2*t*x^2 - 2*t*x -
      2*x^4 - 6*x^3 - 3*x^2) * ht

private abbrev R (p : ℕ) := ZMod (p ^ 4)

private lemma fourth_zero (p : ℕ) : (p : R p) ^ 4 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma index_unit (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    IsUnit (k : R p) := by
  apply (ZMod.isUnit_iff_coprime k (p ^ 4)).mpr
  exact ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk hkp)).symm).pow_right _

private lemma binomial_sq_scaled (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (k : R p) ^ 4 * (b p k : R p) ^ 2 =
      (p : R p) ^ 2 * k ^ 2 - 2 * (p : R p) ^ 3 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hz : k = 0
    · subst k
      simp only [b, Nat.zero_add, Nat.choose_one_right, Nat.add_sub_cancel,
        Nat.cast_mul, Nat.cast_one, one_pow, mul_one, one_mul]
      rw [Nat.cast_sub hp.one_le]
      push_cast
      linear_combination fourth_zero p
    have hprev := ih (by omega)
    have hrec : ((k : R p) + 1) ^ 2 * (b p (k + 1) : R p) =
        (((p : R p) - k - 1) * (p + k)) * (b p k : R p) := by
      have h := congrArg (fun z : ℕ => (z : R p)) (b_step p k hp.pos)
      push_cast [Nat.cast_sub (by omega : k ≤ p - 1), Nat.cast_sub hp.one_le] at h
      convert h using 1 <;> ring
    have hs := congrArg (fun z : R p => z ^ 2) hrec
    push_cast
    apply ((index_unit p k hp (by omega) (by omega)).pow 4).mul_left_cancel
    calc
      _ = (((p : R p) - k - 1) * (p + k)) ^ 2 *
          ((k : R p) ^ 4 * (b p k : R p) ^ 2) := by
            linear_combination (k : R p) ^ 4 * hs
      _ = _ := by rw [hprev]; exact transport (p : R p) k (fourth_zero p)

private lemma weighted_term (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (k : R p) ^ 5 * ((p - 1).choose k : R p) ^ 2 *
        ((p + k - 1).choose k : R p) ^ 2 =
      (p : R p) ^ 2 * k ^ 3 - 2 * (p : R p) ^ 3 * k ^ 2 := by
  have h := binomial_sq_scaled p hp k hk
  simp only [b, Nat.cast_mul] at h
  linear_combination (k : R p) * h

end D5.S3.ArithSums.A357512PrimeDivisibility
