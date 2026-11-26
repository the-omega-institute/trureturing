/- GID: D5/S1/Recurrence/MatharA027182ClosedForm
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharA027182ClosedForm
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The A027182 self-convolution has a closed form in central binomials and powers of two. -/

import D5.S1.Recurrence.MatharA027182SelfConvolution

/-! # Closed form of the A027182 self-convolution

The middle coefficient `a n = [x^n] g_n(x)^2` of the squared row polynomial equals
`4 C(2n+4, n+2) + 4 C(2n+2, n+1) + C(2n, n) - 72 * 2^n + 16 n + 40` for every `n`.
-/

namespace D5.S1.Recurrence.MatharA027182ClosedForm

open D5.S1.Recurrence.MatharA027182SelfConvolution
open Finset Polynomial

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
  simp only [Nat.sub_zero, Nat.choose_eq_zero_of_lt (show n < n+1 by omega), mul_zero,
    add_zero] at h
  convert (congrArg (fun x : ℕ => (x : ℤ)) h).symm using 1
  · push_cast
    ring
  · congr 2
    omega

private theorem closed_form_aux (n : ℕ) :
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
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, mul_assoc, sum_const, card_range,
        nsmul_eq_mul]
      rw [hAA, hAB, hBB, hA, hB]
      push_cast
      ring

/-- For every natural `n`, the self-convolution coefficient `a n` equals
`4 C(2n+4, n+2) + 4 C(2n+2, n+1) + C(2n, n) - 72 * 2^n + 16 n + 40`. -/
theorem closed_form (n : ℕ) :
    (a n : ℤ) = 4 * ((2 * n + 4).choose (n + 2) : ℤ) + 4 * ((2 * n + 2).choose (n + 1) : ℤ)
      + ((2 * n).choose n : ℤ) - 72 * 2 ^ n + 16 * n + 40 := by
  rw [closed_form_aux n, show 2 * (n + 2) = 2 * n + 4 by ring,
    show 2 * (n + 1) = 2 * n + 2 by ring]

end D5.S1.Recurrence.MatharA027182ClosedForm
