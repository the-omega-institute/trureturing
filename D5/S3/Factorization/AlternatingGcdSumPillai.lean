/- GID: D5/S3/Factorization/AlternatingGcdSumPillai
   generality: G
   mirror-B: D5/B/S3/Factorization/AlternatingGcdSumPillai
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bala's alternating gcd sum equals the floor-square totient sequence. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Finset

namespace D5.S3.Factorization.AlternatingGcdSumPillai

/-- OEIS A344598, with division and subtraction in the natural numbers. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 n, Nat.totient k * ((n / k)^2 - ((n - 1) / k)^2)

/-- Pillai's gcd-sum function. -/
def pillai (n : ℕ) : ℕ := ∑ k ∈ Icc 1 n, Nat.gcd k n

/-- The integer-valued alternating sum in Bala's conjecture. -/
def altGcdSum (n : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 (2*n), (-1 : ℤ)^k * Nat.gcd k (4*n)

private lemma sum_Icc_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  rw [show Icc 1 n = Ico 1 (n+1) by ext k; simp,
    sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private lemma pillai_range (n : ℕ) : pillai n = ∑ k ∈ range n, Nat.gcd k n := by
  have h := sum_range_succ' (fun k => Nat.gcd k n) n
  rw [sum_range_succ] at h
  simp only [Nat.gcd_self, Nat.gcd_zero_left] at h
  rw [pillai, sum_Icc_shift]
  omega

private lemma pillai_divisors (n : ℕ) (hn : n ≠ 0) :
    pillai n = ∑ d ∈ n.divisors, Nat.totient d * (n / d) := by
  have hm : ∀ k ∈ range n, Nat.gcd n k ∈ n.divisors := by
    intro k hk
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn⟩
  calc
    pillai n = ∑ k ∈ range n, Nat.gcd n k := by
      simp only [pillai_range, Nat.gcd_comm]
    _ = ∑ d ∈ n.divisors, ∑ k ∈ range n with Nat.gcd n k = d, d :=
      (sum_fiberwise_of_maps_to' hm id).symm
    _ = ∑ d ∈ n.divisors, Nat.totient (n/d) * d := by
      apply sum_congr rfl
      intro d hd
      rw [sum_const, nsmul_eq_mul,
        ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
      simp only [Nat.cast_id]
    _ = ∑ d ∈ n.divisors, Nat.totient d * (n/d) := by
      rw [← Nat.sum_div_divisors n (fun d => Nat.totient d * (n/d))]
      apply sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn]

private lemma square_jump (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (((n/k)^2 - ((n-1)/k)^2 : ℕ) : ℤ) =
      if k ∣ n then (2 : ℤ)*(n/k : ℕ) - 1 else 0 := by
  have hrem := Nat.mod_lt n (by omega : 0 < k)
  have hdiv := Nat.div_add_mod n k
  have hsub : n-1+1 = n := by omega
  by_cases hd : k ∣ n
  · rw [if_pos hd]
    have hr : n % k = 0 := Nat.mod_eq_zero_of_dvd hd
    have hq : 1 ≤ n/k := by nlinarith
    have hpred : (n-1)/k = n/k-1 := by
      apply Nat.div_eq_of_lt_le <;> nlinarith [Nat.sub_add_cancel hq]
    have hsq : (n/k-1)^2 ≤ (n/k)^2 := by nlinarith [Nat.sub_add_cancel hq]
    rw [hpred, Nat.cast_sub hsq]
    simp only [Nat.cast_pow]
    have hc : ((n/k-1 : ℕ) : ℤ) + 1 = (n/k : ℕ) := by
      exact_mod_cast Nat.sub_add_cancel hq
    nlinarith
  · rw [if_neg hd]
    have hr : 0 < n % k := Nat.pos_of_ne_zero (by
      intro h
      exact hd (Nat.dvd_of_mod_eq_zero h))
    have hpred : (n-1)/k = n/k := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    simp [hpred]

/-- The floor-square increments give twice Pillai's function minus the index. -/
theorem a_eq_two_pillai_sub (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = 2*(pillai n : ℤ) - n := by
  have hsum : (a n : ℤ) = ∑ d ∈ n.divisors,
      (Nat.totient d : ℤ) * (2*(n/d : ℕ) - 1) := by
    calc
      (a n : ℤ) = ∑ k ∈ Icc 1 n,
          if k ∣ n then (Nat.totient k : ℤ) * (2*(n/k : ℕ) - 1) else 0 := by
        unfold a
        rw [Nat.cast_sum]
        apply sum_congr rfl
        intro k hk
        rw [Nat.cast_mul, square_jump n k hn (mem_Icc.mp hk).1]
        split_ifs <;> simp
      _ = _ := by
        rw [← sum_filter]
        congr 1
  have hp : (pillai n : ℤ) = ∑ d ∈ n.divisors,
      (Nat.totient d : ℤ) * (n/d : ℕ) := by
    exact_mod_cast pillai_divisors n (by omega)
  have ht : (∑ d ∈ n.divisors, (Nat.totient d : ℤ)) = n := by
    exact_mod_cast Nat.sum_totient n
  rw [hsum]
  simp_rw [mul_sub, mul_one, mul_left_comm (Nat.totient _ : ℤ) 2]
  rw [sum_sub_distrib, ← mul_sum, ← hp, ht]

private lemma sum_parity {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ range (2*n), f k =
      (∑ k ∈ range n, f (2*k)) + ∑ k ∈ range n, f (2*k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ]
    simp only [show 2*n+2 = (2*n+1)+1 by omega, sum_range_succ, ih]
    ac_rfl

private lemma gcd_odd_double (k n : ℕ) :
    Nat.gcd (2*k+1) (2*n) = Nat.gcd (2*k+1) n := by
  apply Nat.Coprime.gcd_mul_left_cancel_right
  exact (show Odd (2*k+1) from ⟨k, by omega⟩).coprime_two_left

private lemma pillai_double (n : ℕ) :
    pillai (2*n) = 2*pillai n + ∑ k ∈ range n, Nat.gcd (2*k+1) n := by
  simp only [pillai_range, sum_parity, Nat.gcd_mul_left, gcd_odd_double, mul_sum]

/-- Splitting into even and odd residue classes gives the doubling identity. -/
theorem pillai_four_mul (n : ℕ) :
    pillai (4*n) + 4*pillai n = 4*pillai (2*n) := by
  have h₁ := pillai_double n
  have h₂ := pillai_double (2*n)
  have ho : (∑ k ∈ range (2*n), Nat.gcd (2*k+1) (2*n)) =
      2 * ∑ k ∈ range n, Nat.gcd (2*k+1) n := by
    simp only [gcd_odd_double]
    rw [show 2*n = n+n by omega, sum_range_add]
    have ht : (∑ k ∈ range n, Nat.gcd (2*(n+k)+1) n) =
        ∑ k ∈ range n, Nat.gcd (2*k+1) n := by
      apply sum_congr rfl
      intro k hk
      rw [show 2*(n+k)+1 = (2*k+1)+2*n by omega, Nat.gcd_add_mul_right_left]
    rw [ht]
    omega
  rw [ho, show 2*(2*n) = 4*n by omega] at h₂
  omega

private lemma signed_reflect (n k : ℕ) (hk : k ≤ 4*n) :
    (-1 : ℤ)^(4*n-k) * Nat.gcd (4*n-k) (4*n) =
      (-1 : ℤ)^k * Nat.gcd k (4*n) := by
  rw [Nat.gcd_self_sub_left hk]
  have hp : Even (4*n-k) ↔ Even k := by
    simp only [Nat.even_iff]
    omega
  simp only [neg_one_pow_eq_ite, hp]

private lemma full_alternating (n : ℕ) :
    (∑ k ∈ range (4*n), (-1 : ℤ)^k * Nat.gcd k (4*n)) =
      4*(pillai (2*n) : ℤ) - pillai (4*n) := by
  have hp := sum_parity (fun k => (Nat.gcd k (4*n) : ℤ)) (2*n)
  have hs := sum_parity (fun k => (-1 : ℤ)^k * Nat.gcd k (4*n)) (2*n)
  have he : (∑ k ∈ range (2*n), (Nat.gcd (2*k) (4*n) : ℤ)) =
      2*(pillai (2*n) : ℤ) := by
    rw [show 4*n = 2*(2*n) by omega]
    simp only [Nat.gcd_mul_left, Nat.cast_mul, Nat.cast_ofNat, ← mul_sum,
      pillai_range, Nat.cast_sum]
  rw [show 2*(2*n) = 4*n by omega, ← Nat.cast_sum, ← pillai_range, he] at hp
  simp only [show 2*(2*n) = 4*n by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, one_mul, pow_one, neg_mul, sum_neg_distrib] at hs
  rw [he] at hs
  linarith

/-- Reflection supplies the two endpoint terms in the alternating half-sum. -/
theorem altGcdSum_eq (n : ℕ) (_hn : 1 ≤ n) :
    2*altGcdSum n + 2*n = 4*(pillai (2*n) : ℤ) - pillai (4*n) := by
  let f : ℕ → ℤ := fun k => (-1 : ℤ)^k * Nat.gcd k (4*n)
  have hs : altGcdSum n = ∑ k ∈ range (2*n), f (k+1) := by
    exact sum_Icc_shift f (2*n)
  have hends : (∑ k ∈ range (2*n), f k) = altGcdSum n + 2*n := by
    have h := sum_range_succ' f (2*n)
    rw [sum_range_succ, ← hs] at h
    have hzero : f 0 = 4*n := by simp [f]
    have hmid : f (2*n) = 2*n := by
      dsimp [f]
      rw [show 4*n = (2*n)*2 by omega, Nat.gcd_mul_right_right]
      simp [pow_mul]
    rw [hzero, hmid] at h
    linarith
  have hupper : (∑ k ∈ range (2*n), f (2*n+k)) = altGcdSum n := by
    rw [hs, ← sum_range_reflect (fun k => f (k+1)) (2*n)]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.mp hk
    have hr := signed_reflect n (2*n+k) (by omega)
    have he : 4*n-(2*n+k) = 2*n-1-k+1 := by omega
    rw [he] at hr
    exact hr.symm
  have hfull := full_alternating n
  change (∑ k ∈ range (4*n), f k) = _ at hfull
  rw [show 4*n = 2*n+2*n by omega, sum_range_add, hends, hupper] at hfull
  rw [show 2*n+2*n = 4*n by omega] at hfull
  linarith

/-- Peter Bala's conjectured alternating gcd formula for OEIS A344598. -/
theorem bala_conjecture (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = altGcdSum n := by
  have ha := a_eq_two_pillai_sub n hn
  have hs := altGcdSum_eq n hn
  have hp : (pillai (4*n) : ℤ) + 4*pillai n = 4*pillai (2*n) := by
    exact_mod_cast pillai_four_mul n
  linarith

#print axioms a_eq_two_pillai_sub
#print axioms pillai_four_mul
#print axioms altGcdSum_eq
#print axioms bala_conjecture

end D5.S3.Factorization.AlternatingGcdSumPillai
