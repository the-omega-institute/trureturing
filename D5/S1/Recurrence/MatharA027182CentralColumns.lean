/- GID: D5/S1/Recurrence/MatharA027182CentralColumns
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharA027182CentralColumns
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The middle columns T(2n,n) and T(2n-1,n-1) satisfy one three-term recurrence. -/

import D5.S1.Recurrence.MatharA027182SelfConvolution

/-! # A shared recurrence for two middle columns

For the triangle `T(n,k) = t(n,k) - 4` with
`t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k)`, the central entries
`u n = T(2n, n)` and the adjacent entries `v n = T(2n-1, n-1)` both satisfy
`2(n+1) f(n) - (7n+5) f(n-1) + 2(3-2n) f(n-2) + 12(1-3n) = 0`, for `n ≥ 2` and `n ≥ 3`
respectively.
-/

namespace D5.S1.Recurrence.MatharA027182CentralColumns

open D5.S1.Recurrence.MatharA027182SelfConvolution

/-- The central column `T(2n, n)` (OEIS A027171). -/
def u (n : ℕ) : ℤ := (T (2 * n) n : ℤ)

/-- The adjacent column `T(2n-1, n-1)` (OEIS A027175). -/
def v (n : ℕ) : ℤ := (T (2 * n - 1) (n - 1) : ℤ)

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

private lemma two_mul_choose (m : ℕ) : 2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) := by
  rw [Nat.centralBinom, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
    Nat.choose_succ_succ, Nat.choose_symm_half]
  ring

private lemma ratio (j : ℕ) :
    ((j : ℤ) + 1) * (Nat.centralBinom (j + 1) : ℤ) =
      2 * (2 * (j : ℤ) + 1) * (Nat.centralBinom j : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ j

private lemma combine (m : ℕ) (f : ℕ → ℤ)
    (e1 : ((m : ℤ) + 1) * f (m + 1) = 2 * (2 * (m : ℤ) + 1) * f m)
    (e2 : ((m : ℤ) + 2) * f (m + 2) = 2 * (2 * (m : ℤ) + 3) * f (m + 1))
    (e3 : ((m : ℤ) + 3) * f (m + 3) = 2 * (2 * (m : ℤ) + 5) * f (m + 2)) :
    2 * ((m : ℤ) + 2 + 1) * (2 * f (m + 3) + f (m + 2) - 4)
      - (7 * ((m : ℤ) + 2) + 5) * (2 * f (m + 2) + f (m + 1) - 4)
      + 2 * (3 - 2 * ((m : ℤ) + 2)) * (2 * f (m + 1) + f m - 4)
      + 12 * (1 - 3 * ((m : ℤ) + 2)) = 0 := by
  linear_combination 4 * e3 + 4 * e2 + e1

private lemma u_eq (j : ℕ) :
    u j = 2 * (Nat.centralBinom (j + 1) : ℤ) + (Nat.centralBinom j : ℤ) - 4 := by
  unfold u
  rw [T_cast (2 * j) j (by omega), Nat.centralBinom, Nat.centralBinom,
    show 2 * j + 2 = 2 * (j + 1) by ring]

private lemma v_eq (j : ℕ) :
    v (j + 1) = 2 * ((2 * (j + 1) + 1).choose (j + 1) : ℤ) +
      ((2 * j + 1).choose j : ℤ) - 4 := by
  unfold v
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show j + 1 - 1 = j by omega,
    T_cast (2 * j + 1) j (by omega), show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring]

/-- For every `n ≥ 2`, the central column `u n = T(2n, n)` satisfies
`2(n+1) u(n) - (7n+5) u(n-1) + 2(3-2n) u(n-2) + 12(1-3n) = 0`. -/
theorem u_recurrence (n : ℕ) (hn : 2 ≤ n) :
    2 * ((n : ℤ) + 1) * u n - (7 * (n : ℤ) + 5) * u (n - 1)
      + 2 * (3 - 2 * (n : ℤ)) * u (n - 2) + 12 * (1 - 3 * (n : ℤ)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    u_eq (m + 2), u_eq (m + 1), u_eq m]
  have e1 := ratio m
  have e2 := ratio (m + 1)
  have e3 := ratio (m + 2)
  push_cast at e1 e2 e3 ⊢
  have := combine m (fun j => (Nat.centralBinom j : ℤ)) (by linarith) (by linarith)
    (by linarith)
  simpa using this

private lemma v_half (j : ℕ) : 2 * v (j + 1) = u (j + 1) - 4 := by
  rw [v_eq, u_eq (j + 1)]
  have h1 : (2 : ℤ) * ((2 * (j + 1) + 1).choose (j + 1) : ℤ) = Nat.centralBinom (j + 2) := by
    exact_mod_cast two_mul_choose (j + 1)
  have h2 : (2 : ℤ) * ((2 * j + 1).choose j : ℤ) = Nat.centralBinom (j + 1) := by
    exact_mod_cast two_mul_choose j
  linear_combination 2 * h1 + h2

/-- For every `n ≥ 3`, the adjacent column `v n = T(2n-1, n-1)` satisfies
`2(n+1) v(n) - (7n+5) v(n-1) + 2(3-2n) v(n-2) + 12(1-3n) = 0`. -/
theorem v_recurrence (n : ℕ) (hn : 3 ≤ n) :
    2 * ((n : ℤ) + 1) * v n - (7 * (n : ℤ) + 5) * v (n - 1)
      + 2 * (3 - 2 * (n : ℤ)) * v (n - 2) + 12 * (1 - 3 * (n : ℤ)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hu := u_recurrence (m + 3) (by omega)
  rw [show m + 3 - 1 = m + 1 + 1 by omega, show m + 3 - 2 = m + 1 by omega] at hu ⊢
  have h3 := v_half (m + 2)
  have h2 := v_half (m + 1)
  have h1 := v_half m
  push_cast at hu h1 h2 h3 ⊢
  have key : 2 * (2 * ((m : ℤ) + 3 + 1) * v (m + 2 + 1)
      - (7 * ((m : ℤ) + 3) + 5) * v (m + 1 + 1)
      + 2 * (3 - 2 * ((m : ℤ) + 3)) * v (m + 1) + 12 * (1 - 3 * ((m : ℤ) + 3))) = 0 := by
    linear_combination hu + 2 * ((m : ℤ) + 3 + 1) * h3 - (7 * ((m : ℤ) + 3) + 5) * h2
      + 2 * (3 - 2 * ((m : ℤ) + 3)) * h1
  have e : m + 3 = m + 2 + 1 := by omega
  rw [e]
  linarith

end D5.S1.Recurrence.MatharA027182CentralColumns
