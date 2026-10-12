/- GID: D5/S3/Zeros/NegativeIndexFibonacciFactorization
   generality: I
   mirror-B: D5/B/S3/Zeros/NegativeIndexFibonacciFactorization
   mirror-E: none(waiver:general-polynomial-identity)
   anchors: []
   utility: none
   digest: Mane's negative-index factorization holds for all k >= 2 and 2 <= s <= k+1. -/

/- result:
   proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#14688; Proved)
   Direct frozen dependencies:
     D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.a
       statement_id: sha256:707a746ffc71d0322be55a448cd0ae6f8377a188517e46b39e67254c7c1c8bb8
     D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.F
       statement_id: sha256:5eb2e2fbbe5f3cc992db084d263b52ee2570682c7751977fdc2376e0b8e00dff
   Definitions: claim, A, P, B; proof_shape: not-applicable (definition).
   a_zero: proof_shape: bind-only; consumers: a_at_k, A_identity.
   a_small: proof_shape: bind-only; consumers: a_at_k, A_identity.
   a_step: proof_shape: bind-only; consumers: a_short, a_at_k.
   a_short: proof_shape: bind-only; consumer: A_identity.
   a_at_k: proof_shape: bind-only; consumer: A_identity.
   B_eq: proof_shape: bind-only; consumer: A_identity.
   A_identity: proof_shape: bind-only; consumer: A_trunc.
   P_degree: proof_shape: bind-only; consumer: B_coeff_high.
   B_pow: proof_shape: bind-only; consumers: B_coeff, B_coeff_mid, A_trunc.
   B_coeff: proof_shape: bind-only; consumers: B_coeff_low, B_coeff_high.
   B_coeff_low: proof_shape: bind-only; consumer: G_coeff_diag.
   B_coeff_high: proof_shape: bind-only; consumer: G_coeff_diag.
   B_coeff_mid: proof_shape: bind-only; consumer: G_coeff_diag.
   A_trunc: proof_shape: bind-only; consumer: a_factor.
   G_coeff_diag: proof_shape: bind-only; consumer: a_factor.
   a_factor: proof_shape: bind-only; consumer: result.
   Utility is none: the identity is universal in k and s, rather than a finite computation.
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Zeros.NegativeIndexTribonacciAttainmentRefutation
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option maxRecDepth 2000

namespace D5.S3.Zeros.NegativeIndexFibonacciFactorization
open Polynomial
open D5.S3.Zeros.NegativeIndexTribonacciAttainmentRefutation (a F)

def claim : Prop := ∀ k : ℕ, k ≥ 2 → ∀ s : ℕ, 2 ≤ s → s ≤ k + 1 →
  F k (-((s * k : ℕ) : ℤ)) =
    -X * (X ^ k + 1) ^ (s - 2) * (X ^ k + C (s : ℤ))

private theorem a_zero (k : ℕ) : a k 0 = 1 := by
  rw [a]; simp only [ite_true]

private theorem a_small (k m : ℕ) (hm : m ≠ 0) (h : m < k) : a k m = 0 := by
  rw [a, if_neg hm, if_pos (Or.inr h)]

private theorem a_step (k m : ℕ) (hk : 2 ≤ k) :
    a k (m + k) = a k m -
      ∑ j ∈ Finset.range (k - 1), X ^ (k - (j + 1)) * a k (m + j + 1) := by
  rw [a, if_neg (by omega : m + k ≠ 0),
    if_neg (by omega : ¬(k = 0 ∨ m + k < k))]
  simp only [Nat.add_sub_cancel]
  simpa only [Nat.add_assoc] using congrArg (fun p => a k m - p)
    (Fin.sum_univ_eq_sum_range
      (fun j => X ^ (k - (j + 1)) * a k (m + (j + 1))) (k - 1))

private theorem a_short (k m : ℕ) (hk : 2 ≤ k) :
    a k (m + k + 1) = (1 + X ^ k) * a k (m + 1) - X * a k m := by
  have h0 := a_step k m hk
  have h1 := a_step k (m + 1) hk
  have hsum :
      (∑ j ∈ Finset.range (k - 1), X ^ (k - (j + 1)) * a k (m + 1 + j + 1)) +
        X ^ k * a k (m + 1) =
      X * (∑ j ∈ Finset.range (k - 1), X ^ (k - (j + 1)) * a k (m + j + 1)) +
        X * a k (m + k) := by
    let g : ℕ → Polynomial ℤ := fun j => X ^ (k - j) * a k (m + j + 1)
    have ht := (Finset.sum_range_succ' g (k - 1)).symm.trans
      (Finset.sum_range_succ g (k - 1))
    have hleft : (∑ j ∈ Finset.range (k - 1), g (j + 1)) =
        ∑ j ∈ Finset.range (k - 1), X ^ (k - (j + 1)) * a k (m + 1 + j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [g]
      congr 2
      omega
    have hright : (∑ j ∈ Finset.range (k - 1), g j) =
        X * ∑ j ∈ Finset.range (k - 1), X ^ (k - (j + 1)) * a k (m + j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      dsimp [g]
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [hleft, hright] at ht
    simpa [g, show k - (k - 1) = 1 by omega,
      show m + (k - 1) + 1 = m + k by omega] using ht
  have hind : m + 1 + k = m + k + 1 := by omega
  rw [hind] at h1
  linear_combination h1 - X * h0 - hsum

private theorem a_at_k (k : ℕ) (hk : 2 ≤ k) : a k k = 1 := by
  have h := a_step k 0 hk
  have hs : (∑ j ∈ Finset.range (k - 1), X ^ (k - (j + 1)) * a k (0 + j + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [a_small k (0 + j + 1) (by omega) (by omega), mul_zero]
  rw [hs, a_zero] at h
  simpa using h

private noncomputable def A (k : ℕ) : PowerSeries (Polynomial ℤ) := PowerSeries.mk (a k)
private noncomputable def P (k : ℕ) : Polynomial (Polynomial ℤ) :=
  C (1 + X ^ k) - C X * X
private noncomputable def B (k : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.X ^ k * (P k : PowerSeries (Polynomial ℤ))

private theorem B_eq (k : ℕ) : B k =
    PowerSeries.C (1 + X ^ k) * PowerSeries.X ^ k -
      PowerSeries.C X * PowerSeries.X ^ (k + 1) := by
  simp only [B, P, Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_mul,
    Polynomial.coe_X, pow_succ]
  ring

private theorem A_identity (k : ℕ) (hk : 2 ≤ k) :
    A k * (1 - B k) = 1 - PowerSeries.C (X ^ k) * PowerSeries.X ^ k := by
  rw [B_eq, mul_sub, mul_one, mul_sub]
  simp only [← mul_assoc]
  apply PowerSeries.ext
  intro m
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C, map_sub,
    A, PowerSeries.coeff_mk, PowerSeries.coeff_one, PowerSeries.coeff_C]
  by_cases hm0 : m = 0
  · subst m
    simp [a_zero, show ¬k ≤ 0 by omega, show ¬k + 1 ≤ 0 by omega ]
  by_cases hml : m < k
  · simp [a_small k m hm0 hml, hm0, show ¬k ≤ m by omega,
      show ¬k + 1 ≤ m by omega]
  by_cases hme : m = k
  · subst m
    simp [a_at_k k hk, a_zero, show k ≠ 0 by omega]
  have hm : k + 1 ≤ m := by omega
  have hr := a_short k (m - (k + 1)) hk
  have he : m - (k + 1) + k + 1 = m := by omega
  have he1 : m - (k + 1) + 1 = m - k := by omega
  rw [he, he1] at hr
  simp only [if_pos (show k ≤ m by omega), if_pos hm, if_neg hm0,
    if_neg (show m - k ≠ 0 by omega)]
  rw [hr]
  ring

private theorem P_degree (k : ℕ) : (P k).natDegree ≤ 1 := by
  have he : P k = C (-X) * X + C (1 + X ^ k) := by
    unfold P
    rw [map_neg]
    ring
  rw [he]
  exact Polynomial.natDegree_linear_le

private theorem B_pow (k r : ℕ) : B k ^ r =
    PowerSeries.X ^ (k * r) * (((P k) ^ r : Polynomial (Polynomial ℤ)) : PowerSeries (Polynomial ℤ)) := by
  simp only [B, mul_pow, ← pow_mul, Polynomial.coe_pow]

private theorem B_coeff (k r m : ℕ) : PowerSeries.coeff m (B k ^ r) =
    if k * r ≤ m then ((P k) ^ r).coeff (m - k * r) else 0 := by
  rw [B_pow, PowerSeries.coeff_X_pow_mul']
  simp only [Polynomial.coeff_coe]

private theorem B_coeff_low (k r m : ℕ) (h : m < k * r) :
    PowerSeries.coeff m (B k ^ r) = 0 := by
  rw [B_coeff, if_neg (not_le.mpr h)]

private theorem B_coeff_high (k r m : ℕ) (h : (k + 1) * r < m) :
    PowerSeries.coeff m (B k ^ r) = 0 := by
  rw [B_coeff]
  split_ifs with hn
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hd : ((P k) ^ r).natDegree ≤ r := by
      calc
        _ ≤ r * (P k).natDegree := Polynomial.natDegree_pow_le
        _ ≤ r * 1 := Nat.mul_le_mul_left r (P_degree k)
        _ = r := by omega
    have hs : m - k * r + k * r = m := Nat.sub_add_cancel hn
    nlinarith
  · rfl

private theorem B_coeff_mid (k s : ℕ) :
    PowerSeries.coeff (s * k + 1) (B k ^ s) =
      -C (s : ℤ) * X * (1 + X ^ k) ^ (s - 1) := by
  rw [B_pow, show s * k + 1 = 1 + k * s by ring,
    PowerSeries.coeff_X_pow_mul, Polynomial.coe_pow]
  have hp0 : PowerSeries.constantCoeff (P k : PowerSeries (Polynomial ℤ)) = 1 + X ^ k := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
    norm_num
  have hp1 : PowerSeries.coeff 1 (P k : PowerSeries (Polynomial ℤ)) = -X := by
    rw [Polynomial.coeff_coe]
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
    norm_num
  rw [PowerSeries.coeff_one_pow, hp0, hp1]
  simp only [map_natCast]
  ring

private theorem A_trunc (k L m : ℕ) (hk : 2 ≤ k) (hm : m < k * L) :
    a k m = PowerSeries.coeff m
      ((1 - PowerSeries.C (X ^ k) * PowerSeries.X ^ k) *
        ∑ r ∈ Finset.range L, B k ^ r) := by
  have hg : A k * (1 - B k ^ L) =
      (1 - PowerSeries.C (X ^ k) * PowerSeries.X ^ k) *
        ∑ r ∈ Finset.range L, B k ^ r := by
    calc
      _ = A k * ((1 - B k) * ∑ r ∈ Finset.range L, B k ^ r) := by
        rw [mul_neg_geom_sum]
      _ = (A k * (1 - B k)) * ∑ r ∈ Finset.range L, B k ^ r := by ring
      _ = _ := by rw [A_identity k hk]
  have hz : PowerSeries.coeff m (A k * B k ^ L) = 0 := by
    have he : A k * B k ^ L = PowerSeries.X ^ (k * L) *
        (A k * (((P k) ^ L : Polynomial (Polynomial ℤ)) : PowerSeries (Polynomial ℤ))) := by
      rw [B_pow]
      ring
    rw [he, PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hm)]
  have hc := congrArg (PowerSeries.coeff m) hg
  rw [mul_sub, mul_one, map_sub, hz, sub_zero] at hc
  simpa only [A, PowerSeries.coeff_mk] using hc

private theorem G_coeff_diag (k s L : ℕ) (hk : 2 ≤ k) (hs : s ≤ k + 1) (hL : s < L) :
    PowerSeries.coeff (s * k + 1) (∑ r ∈ Finset.range L, B k ^ r) =
      -C (s : ℤ) * X * (1 + X ^ k) ^ (s - 1) := by
  rw [map_sum]
  rw [Finset.sum_eq_single s]
  · exact B_coeff_mid k s
  · intro r hr hrs
    by_cases h : r < s
    · apply B_coeff_high
      have hmul := Nat.mul_le_mul_left (k + 1) (show r + 1 ≤ s by omega)
      nlinarith
    · apply B_coeff_low
      have hmul := Nat.mul_le_mul_left k (show s + 1 ≤ r by omega)
      nlinarith
  · intro hn
    exact (hn (Finset.mem_range.mpr hL)).elim

private theorem a_factor (k s : ℕ) (hk : 2 ≤ k) (hs : 2 ≤ s) (hsk : s ≤ k + 1) :
    a k (s * k + 1) = -X * (X ^ k + 1) ^ (s - 2) * (X ^ k + C (s : ℤ)) := by
  have hbound : s * k + 1 < k * (s + 1) := by nlinarith
  have hshift : s * k + 1 - k = (s - 1) * k + 1 := by
    have he : (s - 1) * k + 1 + k = s * k + 1 := by
      nlinarith [show s - 1 + 1 = s by omega]
    omega
  rw [A_trunc k (s + 1) (s * k + 1) hk hbound]
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', if_pos (show k ≤ s * k + 1 by nlinarith), hshift]
  rw [G_coeff_diag k s (s + 1) hk hsk (by omega),
    G_coeff_diag k (s - 1) (s + 1) hk (by omega) (by omega)]
  have hp : (1 + X ^ k : Polynomial ℤ) ^ (s - 1) = (1 + X ^ k) ^ (s - 2) * (1 + X ^ k) := by
    rw [show s - 1 = s - 2 + 1 by omega, pow_succ]
  have hc : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by omega
  rw [hp, show s - 1-1 = s - 2 by omega, hc, map_sub, map_one]
  ring

theorem result : claim := by
  intro k hk s hs hsk
  unfold F
  have he : (1 - (-((s * k : ℕ) : ℤ))).toNat = s * k + 1 := by omega
  rw [he]
  exact a_factor k s hk hs hsk

end D5.S3.Zeros.NegativeIndexFibonacciFactorization
