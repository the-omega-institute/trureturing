/- GID: D5/S1/Recurrence/MatharA027182SelfConvolution
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharA027182SelfConvolution
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The self-convolution sequence OEIS A027182 satisfies Mathar's recurrence. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#23023; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
All private theorems below have proof_shape bind-only and escape_witness none.
Consumers: t_pascal -> row_cast; row_cast -> row_symm, closed_form;
row_symm, g_coeff -> square_sum; square_sum, sum_A_sq, sum_A, sum_AB -> closed_form;
h_recurrence, operator_factor -> h_annihilated;
closed_form, h_annihilated -> result_shift; result_shift -> result.
The definitions t, T, g, a and claim retain the source expressions.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23110
-/

import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination

namespace D5.S1.Recurrence.MatharA027182SelfConvolution

open scoped BigOperators

/- The source's A027170 definitions, written in their stated order. -/
def t (n k : ℕ) : ℕ :=
  Nat.choose (n + 2) (k + 1) + Nat.choose (n + 1) k +
    Nat.choose (n + 1) (k + 1) + Nat.choose n k

def T (n k : ℕ) : ℕ := t n k - t 0 0 + 1

noncomputable def g (n : ℕ) : Polynomial ℕ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (T n k) * Polynomial.X ^ k

/- The source sequence is indexed from 1; this definition also gives the
   natural extension at index 0 used by the proof outline. -/
noncomputable def a (n : ℕ) : ℕ := (g n ^ 2).coeff n

def claim : Prop :=
  ∀ n : ℕ, 6 ≤ n →
    2 * ((n : ℤ) + 2) * (a n : ℤ)
      + (-17 * (n : ℤ) - 23) * (a (n - 1) : ℤ)
      + (47 * (n : ℤ) + 36) * (a (n - 2) : ℤ)
      + 2 * (-22 * (n : ℤ) - 17) * (a (n - 3) : ℤ)
      + 4 * (-(n : ℤ) + 20) * (a (n - 4) : ℤ)
      + 8 * (2 * (n : ℤ) - 9) * (a (n - 5) : ℤ)
      + 24 * (12 * (n : ℤ) - 47) = 0

end D5.S1.Recurrence.MatharA027182SelfConvolution

namespace D5.S1.Recurrence.MatharA027182SelfConvolution
open Finset Polynomial
set_option maxRecDepth 2000

private theorem t_pascal (n k : ℕ) : t n k = 2 * (n+2).choose (k+1) + n.choose k := by
  unfold t
  have h : (n+2).choose (k+1) = (n+1).choose k + (n+1).choose (k+1) := Nat.choose_succ_succ' (n+1) k
  omega

private theorem row_cast (n k : ℕ) (hk : k ≤ n) :
    (T n k : ℤ) = 2 * ((n+2).choose (k+1) : ℤ) + (n.choose k : ℤ) - 4 := by
  have hp := Nat.choose_pos (show k+1 ≤ n+2 by omega)
  have hn : (n+2).choose (k+1) ≠ 1 := by
    intro he
    have he' := Nat.choose_eq_one_iff.mp he
    omega
  have hb := Nat.choose_pos hk
  have ht : 5 ≤ t n k := by rw [t_pascal]; omega
  unfold T
  have h00 : t 0 0 = 5 := rfl
  rw [h00, Nat.cast_add, Nat.cast_sub ht, t_pascal]
  push_cast
  ring

private theorem row_symm (n k : ℕ) (hk : k ≤ n) : T n (n-k) = T n k := by
  apply Nat.cast_injective (R := ℤ)
  rw [row_cast n (n-k) (by omega), row_cast n k hk]
  have hA : (n+2).choose (n-k+1) = (n+2).choose (k+1) := by
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hA, Nat.choose_symm hk]

private theorem g_coeff (n k : ℕ) (hk : k ≤ n) : (g n).coeff k = T n k := by
  simp [g, Polynomial.finsetSum_coeff, show k < n+1 by omega]

private theorem square_sum (n : ℕ) : a n = ∑ k ∈ range (n+1), (T n k)^2 := by
  rw [a, pow_two, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Finset.mem_range_succ_iff.mp hk
  rw [g_coeff n k hk', g_coeff n (n-k) (by omega), row_symm n k hk', pow_two]


private theorem sum_A_sq (n : ℕ) :
    (∑ k ∈ range (n+1), (((n+2).choose (k+1) : ℕ) : ℤ)^2) =
      ((2*(n+2)).choose (n+2) : ℤ) - 2 := by
  have h := Nat.sum_range_choose_sq (n+2)
  rw [show n+2+1 = (n+1+1)+1 by omega, sum_range_succ, sum_range_succ'] at h
  simp only [Nat.choose_self, Nat.choose_zero_right, one_pow] at h
  have hc : (∑ k ∈ range (n+1), (((n+2).choose (k+1) : ℕ) : ℤ)^2) + 2 =
      ((2*(n+2)).choose (n+2) : ℤ) := by
    exact_mod_cast (by omega :
      (∑ k ∈ range (n+1), ((n+2).choose (k+1))^2) + 2 = (2*(n+2)).choose (n+2))
  omega

private theorem sum_A (n : ℕ) :
    (∑ k ∈ range (n+1), (((n+2).choose (k+1) : ℕ) : ℤ)) = 4 * 2^n - 2 := by
  have h := Nat.sum_range_choose (n+2)
  rw [show n+2+1 = (n+1+1)+1 by omega, sum_range_succ, sum_range_succ'] at h
  simp only [Nat.choose_self, Nat.choose_zero_right] at h
  have hc : (∑ k ∈ range (n+1), (((n+2).choose (k+1) : ℕ) : ℤ)) + 2 = 2^(n+2) := by
    exact_mod_cast (by omega : (∑ k ∈ range (n+1), (n+2).choose (k+1)) + 2 = 2^(n+2))
  rw [pow_add] at hc
  norm_num at hc
  linarith

private theorem sum_AB (n : ℕ) :
    (∑ k ∈ range (n+1), (((n+2).choose (k+1) : ℕ) : ℤ) * (n.choose k : ℤ)) =
      ((2*n+2).choose (n+1) : ℤ) := by
  have h := Nat.add_choose_eq (n+2) n (n+1)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ'] at h
  have heq : (∑ k ∈ range (n+1), (n+2).choose (k+1) * n.choose (n+1-(k+1))) =
      ∑ k ∈ range (n+1), (n+2).choose (k+1) * n.choose k := by
    apply sum_congr rfl
    intro k hk
    rw [show n+1-(k+1) = n-k by omega, Nat.choose_symm (by simpa using hk)]
  rw [heq] at h
  simp only [Nat.sub_zero, Nat.choose_eq_zero_of_lt (show n < n+1 by omega), mul_zero, add_zero] at h
  convert (congrArg (fun x : ℕ => (x : ℤ)) h).symm using 1 <;> push_cast <;> congr 2 <;> omega

private theorem closed_form (n : ℕ) :
    (a n : ℤ) = 4*((2*(n+2)).choose (n+2) : ℤ) +
      4*((2*(n+1)).choose (n+1) : ℤ) + ((2*n).choose n : ℤ) - 72*2^n + 16*n+40 := by
  rw [square_sum, Nat.cast_sum]
  have hB : (∑ k ∈ range (n+1), (n.choose k : ℤ)) = 2^n := by
    exact_mod_cast Nat.sum_range_choose n
  have hBB : (∑ k ∈ range (n+1), (n.choose k : ℤ)^2) = ((2*n).choose n : ℤ) := by
    exact_mod_cast Nat.sum_range_choose_sq n
  have hAA := sum_A_sq n
  have hA := sum_A n
  have hAB := sum_AB n
  have hx : (2*n+2) = 2*(n+1) := (Nat.mul_succ 2 n).symm
  rw [hx] at hAB
  simp_rw [Nat.cast_pow]
  calc
    _ = ∑ k ∈ range (n+1), (4*(((n+2).choose (k+1) : ℤ)^2) +
        4*((n+2).choose (k+1) : ℤ)*(n.choose k : ℤ) + (n.choose k : ℤ)^2 -
        16*((n+2).choose (k+1) : ℤ) - 8*(n.choose k : ℤ) + 16) := by
      apply sum_congr rfl
      intro k hk
      rw [row_cast n k (by simpa using hk)]
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, mul_assoc, sum_const, card_range, nsmul_eq_mul]
      rw [hAA, hAB, hBB, hA, hB]
      push_cast
      ring


private noncomputable def h (n : ℕ) : ℤ :=
  4*(Nat.centralBinom (n+2) : ℤ) + 4*(Nat.centralBinom (n+1) : ℤ) + (Nat.centralBinom n : ℤ)

private theorem h_recurrence (m : ℕ) :
    2*((m:ℤ)+4)*h (m+2) - (7*m+27)*h (m+1) - (4*m+2)*h m = 0 := by
  have q1 := congrArg (fun x : ℕ => (x : ℤ)) (Nat.succ_mul_centralBinom_succ m)
  have q2 := congrArg (fun x : ℕ => (x : ℤ)) (Nat.succ_mul_centralBinom_succ (m+1))
  have q3 := congrArg (fun x : ℕ => (x : ℤ)) (Nat.succ_mul_centralBinom_succ (m+2))
  have q4 := congrArg (fun x : ℕ => (x : ℤ)) (Nat.succ_mul_centralBinom_succ (m+3))
  push_cast at q1 q2 q3 q4
  simp only [h, Nat.add_assoc, Nat.reduceAdd]
  simp only [Nat.add_assoc, Nat.reduceAdd] at q1 q2 q3 q4
  linear_combination 8*q4 + 12*q3 + 6*q2 + q1

private noncomputable def B (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  2*((m:ℤ)+4)*f (m+2) - (7*m+27)*f (m+1) - (4*m+2)*f m

private noncomputable def L (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  2*((m:ℤ)+7)*f (m+5) + (-17*m-108)*f (m+4) + (47*m+271)*f (m+3) +
    (-44*m-254)*f (m+2) + (-4*m+60)*f (m+1) + (16*m+8)*f m

private theorem operator_factor (f : ℕ → ℤ) (m : ℕ) :
    L f m = B f (m+3) - 5*B f (m+2) + 8*B f (m+1) - 4*B f m := by
  simp only [L, B, Nat.cast_add, Nat.cast_ofNat, Nat.add_assoc, Nat.reduceAdd]
  ring

private theorem h_annihilated (m : ℕ) : L h m = 0 := by
  rw [operator_factor]
  have h0 := h_recurrence m
  have h1 := h_recurrence (m+1)
  have h2 := h_recurrence (m+2)
  have h3 := h_recurrence (m+3)
  change B h m = 0 at h0
  change B h (m+1) = 0 at h1
  change B h (m+2) = 0 at h2
  change B h (m+3) = 0 at h3
  rw [h0, h1, h2, h3]
  ring

private theorem result_shift (m : ℕ) :
    L (fun n => (a n : ℤ)) m + 24*(12*((m:ℤ)+5)-47) = 0 := by
  have hh := h_annihilated m
  have hc (n : ℕ) : (a n : ℤ) = h n - 72*2^n + 16*n+40 := by
    simpa only [h, Nat.centralBinom_eq_two_mul_choose] using closed_form n
  unfold L at hh ⊢
  simp_rw [hc]
  simp only [Nat.cast_add, Nat.cast_ofNat, pow_add]
  norm_num
  linear_combination hh

theorem result : D5.S1.Recurrence.MatharA027182SelfConvolution.claim := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
  have hr := result_shift m
  unfold L at hr
  convert hr using 1
  push_cast
  ring


end D5.S1.Recurrence.MatharA027182SelfConvolution
