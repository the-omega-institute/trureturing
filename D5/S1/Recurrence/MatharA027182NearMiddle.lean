/- GID: D5/S1/Recurrence/MatharA027182NearMiddle
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharA027182NearMiddle
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The near-middle column T(2n,n-2) satisfies a three-term recurrence from n=4 on. -/

import D5.S1.Recurrence.MatharA027182SelfConvolution

/-! # A recurrence for the near-middle column

For the triangle `T(n,k) = t(n,k) - 4` with
`t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k)`, the entries `z n = T(2n, n-2)`
satisfy a three-term recurrence with quadratic coefficients for every `n ≥ 4`.
-/

namespace D5.S1.Recurrence.MatharA027182NearMiddle

open D5.S1.Recurrence.MatharA027182SelfConvolution

/-- The near-middle column `T(2n, n-2)` (OEIS A027174), read for `n ≥ 2`. -/
def z (n : ℕ) : ℤ := (T (2 * n) (n - 2) : ℤ)

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

private def B (j : ℕ) : ℤ := ((2 * j).choose (j - 2) : ℤ)

private lemma z_eq (j : ℕ) (hj : 2 ≤ j) : z j = 2 * B (j + 1) + B j - 4 := by
  unfold z B
  rw [T_cast (2 * j) (j - 2) (by omega), show 2 * j + 2 = 2 * (j + 1) by ring,
    show j - 2 + 1 = j + 1 - 2 by omega]

private lemma B_ratio (i : ℕ) :
    ((i : ℤ) + 1) * ((i : ℤ) + 5) * B (i + 3) =
      (2 * (i : ℤ) + 6) * (2 * (i : ℤ) + 5) * B (i + 2) := by
  unfold B
  rw [show 2 * (i + 3) = 2 * i + 5 + 1 by ring, show i + 3 - 2 = i + 1 by omega,
    show 2 * (i + 2) = 2 * i + 4 by ring, show i + 2 - 2 = i by omega]
  have h1 : ((2 * i + 5).choose (i + 1) : ℤ) * ((i + 1 : ℕ) : ℤ) =
      ((2 * i + 5).choose i : ℤ) * ((2 * i + 5 - i : ℕ) : ℤ) := by
    exact_mod_cast Nat.choose_succ_right_eq (2 * i + 5) i
  have h0 : ((2 * i + 5 + 1).choose (i + 1) : ℤ) =
      ((2 * i + 5).choose i : ℤ) + ((2 * i + 5).choose (i + 1) : ℤ) := by
    exact_mod_cast Nat.choose_succ_succ' (2 * i + 5) i
  have h2 : ((2 * i + 4).choose i : ℤ) * ((2 * i + 4 + 1 : ℕ) : ℤ) =
      ((2 * i + 4 + 1).choose i : ℤ) * ((2 * i + 4 + 1 - i : ℕ) : ℤ) := by
    exact_mod_cast Nat.choose_mul_succ_eq (2 * i + 4) i
  rw [show 2 * i + 4 + 1 - i = i + 5 by omega, show 2 * i + 4 + 1 = 2 * i + 5 by ring] at h2
  rw [show 2 * i + 5 - i = i + 5 by omega] at h1
  push_cast at h0 h1 h2 ⊢
  linear_combination ((i : ℤ) + 1) * ((i : ℤ) + 5) * h0 + ((i : ℤ) + 5) * h1
    - (2 * (i : ℤ) + 6) * h2

/-- For every `n ≥ 4`, the near-middle column `z n = T(2n, n-2)` satisfies
`-2(n+3)(139n-175) z(n) + (1279n²+1334n-1089) z(n-1) - 2(167n+121)(2n-3) z(n-2)
+ 12(111n²+456n+229) = 0`. -/
theorem z_recurrence (n : ℕ) (hn : 4 ≤ n) :
    -2 * ((n : ℤ) + 3) * (139 * (n : ℤ) - 175) * z n
      + (1279 * (n : ℤ) ^ 2 + 1334 * (n : ℤ) - 1089) * z (n - 1)
      - 2 * (167 * (n : ℤ) + 121) * (2 * (n : ℤ) - 3) * z (n - 2)
      + 12 * (111 * (n : ℤ) ^ 2 + 456 * (n : ℤ) + 229) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    z_eq (m + 4) (by omega), z_eq (m + 3) (by omega), z_eq (m + 2) (by omega)]
  have e0 := B_ratio m
  have e1 := B_ratio (m + 1)
  have e2 := B_ratio (m + 2)
  push_cast at e0 e1 e2 ⊢
  have key : ((m : ℤ) + 3) * (-2 * ((m : ℤ) + 4 + 3) * (139 * ((m : ℤ) + 4) - 175) *
        (2 * B (m + 4 + 1) + B (m + 4) - 4)
      + (1279 * ((m : ℤ) + 4) ^ 2 + 1334 * ((m : ℤ) + 4) - 1089) *
        (2 * B (m + 3 + 1) + B (m + 3) - 4)
      - 2 * (167 * ((m : ℤ) + 4) + 121) * (2 * ((m : ℤ) + 4) - 3) *
        (2 * B (m + 2 + 1) + B (m + 2) - 4)
      + 12 * (111 * ((m : ℤ) + 4) ^ 2 + 456 * ((m : ℤ) + 4) + 229)) = 0 := by
    linear_combination (167 * ((m : ℤ) + 4) + 121) * e0
      + 8 * (7 * ((m : ℤ) + 4) - 79) * e1 - 4 * (139 * ((m : ℤ) + 4) - 175) * e2
  have hne : ((m : ℤ) + 3) ≠ 0 := by positivity
  exact (mul_eq_zero.mp key).resolve_left hne

end D5.S1.Recurrence.MatharA027182NearMiddle
