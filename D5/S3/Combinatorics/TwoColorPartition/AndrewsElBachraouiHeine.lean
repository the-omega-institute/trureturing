/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiHeine
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiHeine
   mirror-E: none(waiver:finite-nilpotent-q-binomial)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: A finite q-difference recurrence proves the nilpotent q-binomial identity. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiLambert
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiHeine

open scoped BigOperators

/-- The q-binomial identity in a nilpotent ring is an exact finite identity. -/
theorem nilpotent_q_binomial {R : Type*} [CommRing R] (a q z : R) (N : ℕ)
    (hq : q ^ N = 0) (hz : z ^ N = 0) :
    (∏ i ∈ Finset.range N,
      (1 - a * z * q ^ i) * Ring.inverse (1 - z * q ^ i)) =
    ∑ r ∈ Finset.range N, z ^ r *
      ∏ i ∈ Finset.range r, (1 - a * q ^ i) * Ring.inverse (1 - q ^ (i + 1)) := by
  classical
  by_cases hN : N = 0
  · subst N
    have hone : (1 : R) = 0 := by simpa using hq
    simp [hone]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let A (r : ℕ) : R :=
    ∏ i ∈ Finset.range r, (1 - a * q ^ i) * Ring.inverse (1 - q ^ (i + 1))
  let F (t : R) : R :=
    ∏ i ∈ Finset.range N,
      (1 - a * t * q ^ i) * Ring.inverse (1 - t * q ^ i)
  let Q (t : R) : R := ∑ r ∈ Finset.range N, t ^ r * A r
  have hqunit (r : ℕ) : IsUnit (1 - q ^ (r + 1)) := by
    apply IsNilpotent.isUnit_one_sub
    refine ⟨N, ?_⟩
    rw [← pow_mul, Nat.mul_comm, pow_mul, hq, zero_pow (by omega)]
  have hA (r : ℕ) :
      (1 - q ^ (r + 1)) * A (r + 1) = (1 - a * q ^ r) * A r := by
    dsimp only [A]
    rw [Finset.prod_range_succ]
    calc
      _ = (1 - a * q ^ r) *
          (∏ i ∈ Finset.range r,
            (1 - a * q ^ i) * Ring.inverse (1 - q ^ (i + 1))) *
          ((1 - q ^ (r + 1)) * Ring.inverse (1 - q ^ (r + 1))) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ (hqunit r), mul_one]
  have hQ (t : R) (ht : t ^ N = 0) :
      (1 - t) * Q t = (1 - a * t) * Q (t * q) := by
    let B (r : ℕ) := t ^ r * (1 - q ^ r) * A r
    let C (r : ℕ) := t ^ (r + 1) * (1 - a * q ^ r) * A r
    have hBC (r : ℕ) : B (r + 1) = C r := by
      dsimp only [B, C]
      rw [mul_assoc, hA, mul_assoc]
    have hB0 : B 0 = 0 := by simp [B]
    have hCN : C (N - 1) = 0 := by
      simp only [C, show N - 1 + 1 = N by omega, ht, zero_mul]
    have hs : (∑ r ∈ Finset.range N, B r) = ∑ r ∈ Finset.range N, C r := by
      have hleft := Finset.sum_range_succ' B (N - 1)
      have hright := Finset.sum_range_succ C (N - 1)
      rw [show N - 1 + 1 = N by omega, hB0, add_zero] at hleft
      rw [show N - 1 + 1 = N by omega, hCN, add_zero] at hright
      rw [hleft, hright]
      exact Finset.sum_congr rfl (fun r _ => hBC r)
    have hdiff : Q t - Q (t * q) = ∑ r ∈ Finset.range N, B r := by
      dsimp only [Q, B]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_pow]
      ring
    have hshift : t * Q t - a * t * Q (t * q) =
        ∑ r ∈ Finset.range N, C r := by
      dsimp only [Q, C]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_pow, pow_succ]
      ring
    linear_combination hdiff - hshift + hs
  have htunit (t : R) (ht : t ^ N = 0) : IsUnit (1 - t) :=
    IsNilpotent.isUnit_one_sub ⟨N, ht⟩
  have hF (t : R) (ht : t ^ N = 0) :
      (1 - t) * F t = (1 - a * t) * F (t * q) := by
    let f (i : ℕ) := (1 - a * t * q ^ i) * Ring.inverse (1 - t * q ^ i)
    have hlast : f N = 1 := by simp [f, hq]
    have hshift (i : ℕ) : f (i + 1) =
        (1 - a * (t * q) * q ^ i) * Ring.inverse (1 - (t * q) * q ^ i) := by
      dsimp [f]
      congr 2 <;> rw [pow_succ] <;> ring
    have hstep : F t = f 0 * F (t * q) := by
      have hfirst := Finset.prod_range_succ' f N
      have hlast' := Finset.prod_range_succ f N
      rw [hlast, mul_one] at hlast'
      rw [hlast'] at hfirst
      simpa only [F, hshift, mul_comm] using hfirst
    rw [hstep]
    dsimp only [f]
    simp only [pow_zero, mul_one]
    calc
      _ = (1 - a * t) * F (t * q) * ((1 - t) * Ring.inverse (1 - t)) := by
        ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ (htunit t ht), mul_one]
  have hzero : F 0 = Q 0 := by
    dsimp only [Q]
    rw [Finset.sum_eq_single 0]
    · simp [F, A]
    · intro r _ hr
      simp [zero_pow hr]
    · simp [hNpos]
  have hback : ∀ k ≤ N, F (z * q ^ k) = Q (z * q ^ k) := by
    apply Nat.decreasingInduction
    · intro k hk ih
      have ht : (z * q ^ k) ^ N = 0 := by rw [mul_pow, hz, zero_mul]
      apply (htunit _ ht).mul_left_cancel
      rw [hF _ ht, hQ _ ht]
      have hnext : z * q ^ k * q = z * q ^ (k + 1) := by rw [pow_succ, mul_assoc]
      rw [hnext, ih]
    · simpa [hq] using hzero
  simpa only [pow_zero, mul_one, F, Q, A] using hback 0 (Nat.zero_le N)

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiHeine
