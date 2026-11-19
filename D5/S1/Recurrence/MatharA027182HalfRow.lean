/- GID: D5/S1/Recurrence/MatharA027182HalfRow
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharA027182HalfRow
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The half-row sums of T(n,k) satisfy Mathar's seven-term recurrence from n=6 on. -/

import D5.S1.Recurrence.MatharA027182SelfConvolution

/-! # Half-row sums of the A027170 triangle

For the triangle `T(n,k) = t(n,k) - 4` with
`t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k)`, the half-row sums
`b n = ∑_{k ≤ ⌊n/2⌋} T(n,k)` (OEIS A027179) satisfy a seven-term recurrence with quadratic
coefficients for every `n ≥ 6`.
-/

namespace D5.S1.Recurrence.MatharA027182HalfRow

open D5.S1.Recurrence.MatharA027182SelfConvolution
open Finset

/-- The half-row sum `∑_{k=0}^{⌊n/2⌋} T(n,k)` (OEIS A027179). -/
def b (n : ℕ) : ℤ := ∑ k ∈ range (n / 2 + 1), (T n k : ℤ)

private lemma T_cast (n k : ℕ) (hk : k ≤ n) :
    (T n k : ℤ) = 2 * ((n + 2).choose (k + 1) : ℤ) + (n.choose k : ℤ) - 4 := by
  have hp : (n + 2).choose (k + 1) = (n + 1).choose k + (n + 1).choose (k + 1) :=
    Nat.choose_succ_succ (n + 1) k
  have h1 : 1 ≤ (n + 1).choose k := Nat.choose_pos (by omega)
  have h2 : 1 ≤ (n + 1).choose (k + 1) := Nat.choose_pos (by omega)
  have h3 : 1 ≤ n.choose k := Nat.choose_pos hk
  have ht : t n k = 2 * (n + 2).choose (k + 1) + n.choose k := by
    unfold t
    omega
  have h00 : t 0 0 = 5 := by decide
  unfold T
  rw [h00, ht]
  have h5 : 5 ≤ 2 * (n + 2).choose (k + 1) + n.choose k := by omega
  rw [Nat.cast_add, Nat.cast_sub h5]
  push_cast
  ring

private lemma sum_even (p : ℕ) :
    2 * (∑ j ∈ range (p + 1), ((2 * p).choose j : ℤ)) =
      4 ^ p + ((2 * p).choose p : ℤ) := by
  have hodd : (∑ j ∈ range (p + 1), ((2 * p + 1).choose j : ℤ)) = 4 ^ p := by
    exact_mod_cast Nat.sum_range_choose_halfway p
  rw [sum_range_succ'] at hodd
  have hsplit : (∑ j ∈ range p, ((2 * p + 1).choose (j + 1) : ℤ)) =
      (∑ j ∈ range p, ((2 * p).choose j : ℤ)) +
        ∑ j ∈ range p, ((2 * p).choose (j + 1) : ℤ) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    exact_mod_cast Nat.choose_succ_succ' (2 * p) j
  have hfirst : (∑ j ∈ range (p + 1), ((2 * p).choose j : ℤ)) =
      (∑ j ∈ range p, ((2 * p).choose (j + 1) : ℤ)) + 1 := by
    rw [sum_range_succ']
    simp
  have hlast : (∑ j ∈ range (p + 1), ((2 * p).choose j : ℤ)) =
      (∑ j ∈ range p, ((2 * p).choose j : ℤ)) + ((2 * p).choose p : ℤ) := sum_range_succ _ _
  simp only [Nat.choose_zero_right, Nat.cast_one] at hodd
  linarith

private lemma ratio (j : ℕ) :
    ((j : ℤ) + 1) * (Nat.centralBinom (j + 1) : ℤ) =
      2 * (2 * (j : ℤ) + 1) * (Nat.centralBinom j : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ j

private lemma shifted_sum (n m : ℕ) :
    (∑ k ∈ range (m + 1), ((n + 2).choose (k + 1) : ℤ)) =
      (∑ j ∈ range (m + 2), ((n + 2).choose j : ℤ)) - 1 := by
  rw [sum_range_succ' (fun j => ((n + 2).choose j : ℤ)) (m + 1)]
  simp

private lemma b_expand (n : ℕ) :
    b n = 2 * (∑ j ∈ range (n / 2 + 2), ((n + 2).choose j : ℤ)) - 2
      + (∑ k ∈ range (n / 2 + 1), (n.choose k : ℤ)) - 4 * ((n / 2 : ℕ) + 1 : ℤ) := by
  unfold b
  have hc : ∀ k ∈ range (n / 2 + 1),
      (T n k : ℤ) = 2 * ((n + 2).choose (k + 1) : ℤ) + (n.choose k : ℤ) - 4 := by
    intro k hk
    exact T_cast n k (by have := mem_range.mp hk; omega)
  rw [sum_congr rfl hc, sum_sub_distrib, sum_add_distrib, ← mul_sum, shifted_sum]
  simp
  ring

private lemma b_even (q : ℕ) :
    2 * b (2 * q) = 2 * 4 ^ (q + 1) + 2 * (Nat.centralBinom (q + 1) : ℤ) - 4
      + 4 ^ q + (Nat.centralBinom q : ℤ) - 8 * q - 8 := by
  rw [b_expand, show 2 * q / 2 = q by omega]
  have h1 := sum_even (q + 1)
  have h2 := sum_even q
  rw [show 2 * (q + 1) = 2 * q + 2 by ring] at h1
  rw [show q + 1 + 1 = q + 2 by ring] at h1
  simp only [Nat.centralBinom, show 2 * (q + 1) = 2 * q + 2 by ring]
  linarith

private lemma b_odd (q : ℕ) : b (2 * q + 1) = 9 * 4 ^ q - 4 * q - 6 := by
  rw [b_expand, show (2 * q + 1) / 2 = q by omega]
  have h1 : (∑ j ∈ range (q + 1 + 1), ((2 * (q + 1) + 1).choose j : ℤ)) = 4 ^ (q + 1) := by
    exact_mod_cast Nat.sum_range_choose_halfway (q + 1)
  have h2 : (∑ j ∈ range (q + 1), ((2 * q + 1).choose j : ℤ)) = 4 ^ q := by
    exact_mod_cast Nat.sum_range_choose_halfway q
  rw [show 2 * (q + 1) + 1 = 2 * q + 1 + 2 by ring, show q + 1 + 1 = q + 2 by ring] at h1
  rw [h1, h2]
  ring

/-- For every `n ≥ 6`, the half-row sums satisfy Mathar's seven-term recurrence
`∑_{j=0}^{6} p_j(n) b(n-j) + 4(-24n²+196n-365) = 0`. -/
theorem half_row_recurrence (n : ℕ) (hn : 6 ≤ n) :
    -((n : ℤ) + 2) * (3 * (n : ℤ) - 20) * b n
      - ((n : ℤ) + 1) * (3 * (n : ℤ) - 11) * b (n - 1)
      + (33 * (n : ℤ) ^ 2 - 180 * (n : ℤ) - 100) * b (n - 2)
      + (15 * (n : ℤ) ^ 2 - 56 * (n : ℤ) + 1) * b (n - 3)
      + 2 * (-51 * (n : ℤ) ^ 2 + 313 * (n : ℤ) - 208) * b (n - 4)
      - 12 * ((n : ℤ) - 1) * ((n : ℤ) - 4) * b (n - 5)
      + 8 * (9 * (n : ℤ) - 11) * ((n : ℤ) - 5) * b (n - 6)
      + 4 * (-24 * (n : ℤ) ^ 2 + 196 * (n : ℤ) - 365) = 0 := by
  rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
  · obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
    subst hq
    rw [show r + 3 + (r + 3) = 2 * (r + 3) by ring,
      show 2 * (r + 3) - 1 = 2 * (r + 2) + 1 by omega,
      show 2 * (r + 3) - 2 = 2 * (r + 2) by omega,
      show 2 * (r + 3) - 3 = 2 * (r + 1) + 1 by omega,
      show 2 * (r + 3) - 4 = 2 * (r + 1) by omega,
      show 2 * (r + 3) - 5 = 2 * r + 1 by omega,
      show 2 * (r + 3) - 6 = 2 * r by omega]
    have e0 := b_even r
    have e1 := b_even (r + 1)
    have e2 := b_even (r + 2)
    have e3 := b_even (r + 3)
    have o0 := b_odd r
    have o1 := b_odd (r + 1)
    have o2 := b_odd (r + 2)
    have c0 := ratio r
    have c1 := ratio (r + 1)
    have c2 := ratio (r + 2)
    have c3 := ratio (r + 3)
    push_cast at e0 e1 e2 e3 o0 o1 o2 c0 c1 c2 c3 ⊢
    have key : 2 * (-((2 * ((r : ℤ) + 3)) + 2) * (3 * (2 * ((r : ℤ) + 3)) - 20) * b (2 * (r + 3))
      - ((2 * ((r : ℤ) + 3)) + 1) * (3 * (2 * ((r : ℤ) + 3)) - 11) * b (2 * (r + 2) + 1)
      + (33 * (2 * ((r : ℤ) + 3)) ^ 2 - 180 * (2 * ((r : ℤ) + 3)) - 100) * b (2 * (r + 2))
      + (15 * (2 * ((r : ℤ) + 3)) ^ 2 - 56 * (2 * ((r : ℤ) + 3)) + 1) * b (2 * (r + 1) + 1)
      + 2 * (-51 * (2 * ((r : ℤ) + 3)) ^ 2 + 313 * (2 * ((r : ℤ) + 3)) - 208) * b (2 * (r + 1))
      - 12 * ((2 * ((r : ℤ) + 3)) - 1) * ((2 * ((r : ℤ) + 3)) - 4) * b (2 * r + 1)
      + 8 * (9 * (2 * ((r : ℤ) + 3)) - 11) * ((2 * ((r : ℤ) + 3)) - 5) * b (2 * r)
      + 4 * (-24 * (2 * ((r : ℤ) + 3)) ^ 2 + 196 * (2 * ((r : ℤ) + 3)) - 365)) = 0 := by
      linear_combination
        (-((2 * ((r : ℤ) + 3)) + 2) * (3 * (2 * ((r : ℤ) + 3)) - 20)) * e3
        - 2 * (((2 * ((r : ℤ) + 3)) + 1) * (3 * (2 * ((r : ℤ) + 3)) - 11)) * o2
        + (33 * (2 * ((r : ℤ) + 3)) ^ 2 - 180 * (2 * ((r : ℤ) + 3)) - 100) * e2
        + 2 * (15 * (2 * ((r : ℤ) + 3)) ^ 2 - 56 * (2 * ((r : ℤ) + 3)) + 1) * o1
        + 2 * (-51 * (2 * ((r : ℤ) + 3)) ^ 2 + 313 * (2 * ((r : ℤ) + 3)) - 208) * e1
        - 2 * (12 * ((2 * ((r : ℤ) + 3)) - 1) * ((2 * ((r : ℤ) + 3)) - 4)) * o0
        + 8 * (9 * (2 * ((r : ℤ) + 3)) - 11) * ((2 * ((r : ℤ) + 3)) - 5) * e0
        + (-4 * (18 * (r : ℤ) + 43)) * c0 + (-4 * (15 * (r : ℤ) + 22)) * c1
        + (12 * (13 * (r : ℤ) + 4)) * c2 + (-8 * (3 * (r : ℤ) - 1)) * c3
    linarith
  · obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
    subst hq
    rw [show 2 * (r + 3) + 1 - 1 = 2 * (r + 3) by omega,
      show 2 * (r + 3) + 1 - 2 = 2 * (r + 2) + 1 by omega,
      show 2 * (r + 3) + 1 - 3 = 2 * (r + 2) by omega,
      show 2 * (r + 3) + 1 - 4 = 2 * (r + 1) + 1 by omega,
      show 2 * (r + 3) + 1 - 5 = 2 * (r + 1) by omega,
      show 2 * (r + 3) + 1 - 6 = 2 * r + 1 by omega]
    have e1 := b_even (r + 1)
    have e2 := b_even (r + 2)
    have e3 := b_even (r + 3)
    have o0 := b_odd r
    have o1 := b_odd (r + 1)
    have o2 := b_odd (r + 2)
    have o3 := b_odd (r + 3)
    have c1 := ratio (r + 1)
    have c2 := ratio (r + 2)
    have c3 := ratio (r + 3)
    push_cast at e1 e2 e3 o0 o1 o2 o3 c1 c2 c3 ⊢
    have key : 2 * (-((2 * ((r : ℤ) + 3) + 1) + 2) * (3 * (2 * ((r : ℤ) + 3) + 1) - 20)
        * b (2 * (r + 3) + 1)
      - ((2 * ((r : ℤ) + 3) + 1) + 1) * (3 * (2 * ((r : ℤ) + 3) + 1) - 11) * b (2 * (r + 3))
      + (33 * (2 * ((r : ℤ) + 3) + 1) ^ 2 - 180 * (2 * ((r : ℤ) + 3) + 1) - 100)
        * b (2 * (r + 2) + 1)
      + (15 * (2 * ((r : ℤ) + 3) + 1) ^ 2 - 56 * (2 * ((r : ℤ) + 3) + 1) + 1) * b (2 * (r + 2))
      + 2 * (-51 * (2 * ((r : ℤ) + 3) + 1) ^ 2 + 313 * (2 * ((r : ℤ) + 3) + 1) - 208)
        * b (2 * (r + 1) + 1)
      - 12 * ((2 * ((r : ℤ) + 3) + 1) - 1) * ((2 * ((r : ℤ) + 3) + 1) - 4) * b (2 * (r + 1))
      + 8 * (9 * (2 * ((r : ℤ) + 3) + 1) - 11) * ((2 * ((r : ℤ) + 3) + 1) - 5) * b (2 * r + 1)
      + 4 * (-24 * (2 * ((r : ℤ) + 3) + 1) ^ 2 + 196 * (2 * ((r : ℤ) + 3) + 1) - 365)) = 0 := by
      linear_combination
        2 * (-((2 * ((r : ℤ) + 3) + 1) + 2) * (3 * (2 * ((r : ℤ) + 3) + 1) - 20)) * o3
        - (((2 * ((r : ℤ) + 3) + 1) + 1) * (3 * (2 * ((r : ℤ) + 3) + 1) - 11)) * e3
        + 2 * (33 * (2 * ((r : ℤ) + 3) + 1) ^ 2 - 180 * (2 * ((r : ℤ) + 3) + 1) - 100) * o2
        + (15 * (2 * ((r : ℤ) + 3) + 1) ^ 2 - 56 * (2 * ((r : ℤ) + 3) + 1) + 1) * e2
        + 4 * (-51 * (2 * ((r : ℤ) + 3) + 1) ^ 2 + 313 * (2 * ((r : ℤ) + 3) + 1) - 208) * o1
        - (12 * ((2 * ((r : ℤ) + 3) + 1) - 1) * ((2 * ((r : ℤ) + 3) + 1) - 4)) * e1
        + 2 * (8 * (9 * (2 * ((r : ℤ) + 3) + 1) - 11) * ((2 * ((r : ℤ) + 3) + 1) - 5)) * o0
        + (12 * ((r : ℤ) + 3)) * c1 + (4 * (3 * (r : ℤ) + 4)) * c2
        + (-8 * (3 * (r : ℤ) + 5)) * c3
    linarith

end D5.S1.Recurrence.MatharA027182HalfRow
