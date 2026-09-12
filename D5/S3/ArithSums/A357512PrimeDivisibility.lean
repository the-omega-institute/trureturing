/- GID: D5/S3/ArithSums/A357512PrimeDivisibility
   generality: G
   mirror-B: D5/B/S3/ArithSums/A357512PrimeDivisibility
   mirror-E: none(waiver:universal-divisibility-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Fourth-power divisibility of the fifth-weighted Apery sum at indices coprime to six. -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
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
      convert h using 1
      ring
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

-- Exact square-factor reduction for arbitrary positive indices.
private lemma shifted_binomial (n k : ℕ) :
    (k+1)^2 * ((n-1).choose (k+1) * (n+k).choose (k+1)) =
      n * (n-1-k) * ((n-1).choose k * (n+k).choose k) := by
  have h₁ := Nat.choose_succ_right_eq (n-1) k
  have h₂ := Nat.choose_succ_right_eq (n+k) k
  rw [show n+k-k = n by omega] at h₂
  calc
    _ = ((n-1).choose (k+1)*(k+1)) * ((n+k).choose (k+1)*(k+1)) := by ring
    _ = _ := by rw [h₁,h₂]; ring

private lemma weighted_exact (n k : ℕ) :
    (k+1)^5 * ((n-1).choose (k+1))^2 * ((n+k).choose (k+1))^2 =
      n^2 * ((k+1)*(n-1-k)^2 * ((n-1).choose k)^2 * ((n+k).choose k)^2) := by
  have h := congrArg (fun z : ℕ => z^2) (shifted_binomial n k)
  calc
    _ = (k+1) * ((k+1)^2 * ((n-1).choose (k+1) * (n+k).choose (k+1)))^2 := by ring
    _ = _ := by rw [h]; ring

private def reducedSum (n : ℕ) : ℕ :=
  ∑ k ∈ range (n-1), (k+1)*(n-1-k)^2 * ((n-1).choose k)^2 * ((n+k).choose k)^2

private lemma sum_factorization (n : ℕ) (hn : 0 < n) :
    a (n-1) = n^2 * reducedSum n := by
  unfold a reducedSum
  rw [sum_range_succ']
  simp only [zero_pow (by decide : 5 ≠ 0), zero_mul, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [show n-1+(k+1) = n+k by omega]
  exact weighted_exact n k

private def c (n k : ℕ) : ℕ := (n - 1).choose k * (n + k).choose k

private lemma c_step (n k : ℕ) (hk : k < n) :
    (k + 1) ^ 2 * (c n (k + 1) + c n k) = n ^ 2 * c n k := by
  have h₁ := Nat.choose_succ_right_eq (n - 1) k
  have h₂ := Nat.add_one_mul_choose_eq (n + k) k
  have hrec : (k + 1) ^ 2 * c n (k + 1) =
      (n - 1 - k) * (n + k + 1) * c n k := by
    dsimp [c]
    calc
      _ = ((n - 1).choose (k + 1) * (k + 1)) *
          ((n + k + 1).choose (k + 1) * (k + 1)) := by ring
      _ = _ := by rw [h₁, ← h₂]; ring
  have hpoly : (n - 1 - k) * (n + k + 1) + (k + 1) ^ 2 = n ^ 2 := by
    have hsub : n - 1 - k + (k + 1) = n := by omega
    nlinarith
  calc
    _ = ((n - 1 - k) * (n + k + 1) + (k + 1) ^ 2) * c n k := by
      rw [mul_add, hrec]; ring
    _ = _ := by rw [hpoly]

private lemma c_step_linear (n k : ℕ) (hk : k < n) :
    (k + 1) * (c n (k + 1) + c n k) =
      n * ((n - 1).choose k * (n + k).choose (k + 1)) := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1)
  have h := Nat.choose_succ_right_eq (n + k) k
  rw [show n + k - k = n by omega] at h
  calc
    _ = (k + 1) ^ 2 * (c n (k + 1) + c n k) := by ring
    _ = n ^ 2 * c n k := c_step n k hk
    _ = n * (n - 1).choose k * ((n + k).choose k * n) := by dsimp [c]; ring
    _ = n * (n - 1).choose k * ((n + k).choose (k + 1) * (k + 1)) := by rw [h]
    _ = _ := by ring

private lemma telescoping_transport {S : Type*} [CommRing S] (t x u v : S)
    (ht : t ^ 2 = 0) (hq : x ^ 2 * v ^ 2 = x ^ 2 * u ^ 2)
    (hl : t * x * v ^ 2 = t * x * u ^ 2) :
    12 * x * (t - x) ^ 2 * u ^ 2 =
      (3 * x ^ 2 * (x + 1) ^ 2 - 4 * t * x * (x + 1) * (2 * x + 1)) * v ^ 2 -
      (3 * (x - 1) ^ 2 * x ^ 2 - 4 * t * (x - 1) * x * (2 * x - 1)) * u ^ 2 := by
  linear_combination
    -3 * (x + 1) ^ 2 * hq + 4 * (x + 1) * (2 * x + 1) * hl + 12 * x * u ^ 2 * ht

private abbrev Q (n : ℕ) := ZMod (n ^ 2)

private def boundary (n k : ℕ) : Q n :=
  (3 * (k : Q n) ^ 2 * (k + 1) ^ 2 -
    4 * n * k * (k + 1) * (2 * k + 1)) * (c n k : Q n) ^ 2

private lemma reduced_term_telescopes (n k : ℕ) (hk : k < n) :
    12 * (k + 1 : ℕ) * ((n - 1 - k : ℕ) : Q n) ^ 2 * (c n k : Q n) ^ 2 =
      boundary n (k + 1) - boundary n k := by
  have ht : (n : Q n) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hrec := congrArg (fun z : ℕ => (z : Q n)) (c_step n k hk)
  have hlin := congrArg (fun z : ℕ => (z : Q n)) (c_step_linear n k hk)
  push_cast at hrec hlin
  have hq : ((k : Q n) + 1) ^ 2 * (c n (k + 1) : Q n) ^ 2 =
      ((k : Q n) + 1) ^ 2 * (c n k : Q n) ^ 2 := by
    linear_combination
      ((c n (k + 1) : Q n) - c n k) * hrec +
      (c n k : Q n) * ((c n (k + 1) : Q n) - c n k) * ht
  have hl : (n : Q n) * (k + 1) * (c n (k + 1) : Q n) ^ 2 =
      (n : Q n) * (k + 1) * (c n k : Q n) ^ 2 := by
    linear_combination
      (n : Q n) * ((c n (k + 1) : Q n) - c n k) * hlin +
      ((n - 1).choose k : Q n) * ((n + k).choose (k + 1) : Q n) *
        ((c n (k + 1) : Q n) - c n k) * ht
  have h := telescoping_transport (n : Q n) (k + 1) (c n k) (c n (k + 1)) ht hq hl
  have hs : ((n - 1 - k : ℕ) : Q n) = (n : Q n) - (k + 1) := by
    rw [Nat.cast_sub (by omega : k ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  simp only [boundary, hs, Nat.cast_add, Nat.cast_one]
  convert h using 1; ring

private lemma reduced_sum_scaled_zero (n : ℕ) (hn : 0 < n) :
    12 * (reducedSum n : Q n) = 0 := by
  have ht : (n : Q n) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  calc
    _ = ∑ k ∈ range (n - 1),
        12 * (k + 1 : ℕ) * ((n - 1 - k : ℕ) : Q n) ^ 2 * (c n k : Q n) ^ 2 := by
      simp only [reducedSum, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, mul_sum, c]
      apply sum_congr rfl
      intro k hk
      push_cast
      ring
    _ = ∑ k ∈ range (n - 1), (boundary n (k + 1) - boundary n k) := by
      apply sum_congr rfl
      intro k hk
      exact reduced_term_telescopes n k (by have := mem_range.mp hk; omega)
    _ = boundary n (n - 1) - boundary n 0 := sum_range_sub (boundary n) (n - 1)
    _ = (n : Q n) ^ 2 *
        (3 * (n - 1) ^ 2 - 4 * (n - 1) * (2 * (n - 1) + 1)) *
        (c n (n - 1) : Q n) ^ 2 := by
      simp only [boundary, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
        zero_mul, sub_zero, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      ring
    _ = 0 := by rw [ht, zero_mul, zero_mul]

/-- The fifth-weighted Apéry sum is divisible by the fourth power of every odd index
that is not divisible by three, including composite indices. -/
theorem fourth_dvd_of_odd_not_three (n : ℕ) (hn : Odd n) (h3 : ¬3 ∣ n) :
    n ^ 4 ∣ a (n - 1) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hscaled : n ^ 2 ∣ 12 * reducedSum n := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using reduced_sum_scaled_zero n hnpos
  have hc2 : n.Coprime 2 := hn.coprime_two_right
  have hc3 : n.Coprime 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hc12 : n.Coprime 12 := by
    simpa using (hc2.pow_right 2).mul_right hc3
  obtain ⟨q, hq⟩ := (hc12.pow_left 2).dvd_of_dvd_mul_left hscaled
  refine ⟨q, ?_⟩
  rw [sum_factorization n hnpos, hq]
  ring

end D5.S3.ArithSums.A357512PrimeDivisibility
