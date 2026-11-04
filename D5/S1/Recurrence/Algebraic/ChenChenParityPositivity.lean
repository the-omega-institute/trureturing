/- GID: D5/S1/Recurrence/Algebraic/ChenChenParityPositivity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/ChenChenParityPositivity
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Eulerian triangles with integer step at most minus three have positive even rows. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Two-step sign propagation for Chen and Chen's negative-step Eulerian triangles.

The escape audit tracked by issue #24785 remains unresolved: the
`even_rows_positive` registration is `IE-C050 ClosedTruthReadout` under
`source.params`, and the `result` registration is `IE-C050 ClosedTruthReadout`
under `source.unlinked_operand` with operand `Classical.choice`. These are
unresolved audit bindings; no `declared_validated` status is claimed.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.ChenChenParityPositivity

/-- The boundary and interior recursion in OEIS A392664--A392666.
Values outside the triangle, including row zero, are unconstrained. -/
def Source (m : ℤ) (T : ℕ → ℕ → ℤ) : Prop :=
  (∀ n, 1 ≤ n → T n 1 = 1 ∧ T n n = 1) ∧
  ∀ n k, 1 < k → k < n →
    T n k = (m * ((n : ℤ) - (k : ℤ)) + 1) * T (n - 1) (k - 1) +
      (m * ((k : ℤ) - 1) + 1) * T (n - 1) k

/-- Existence together with the assertion about every solution, without
fixing an extension outside the source's triangular domain. -/
def ParityPositivity (m : ℤ) : Prop :=
  (∃ T, Source m T) ∧
    ∀ T, Source m T → ∀ n, 1 ≤ n → Even n →
      ∀ k, 1 ≤ k → k ≤ n → 0 ≤ T n k

/-- The conjunction of the three source conjectures. -/
def claim : Prop :=
  ParityPositivity (-3) ∧ ParityPositivity (-4) ∧ ParityPositivity (-5)

private def triangle (m : ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | n + 1, k => if k = 1 ∨ k = n + 1 then 1 else
      (m * ((n + 1 : ℕ) - (k : ℤ)) + 1) * triangle m n (k - 1) +
        (m * ((k : ℤ) - 1) + 1) * triangle m n k

private theorem source_exists (m : ℤ) : ∃ T, Source m T := by
  refine ⟨triangle m, ?_, ?_⟩
  · intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [triangle]
  · intro n k hk hkn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [triangle, show k ≠ 1 by omega, show k ≠ n + 1 by omega]

private theorem reflection {m : ℤ} {T : ℕ → ℕ → ℤ} (h : Source m T)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    T n k = T n (n + 1 - k) := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hl : k = 1
    · subst k
      simpa using (h.1 n hn).1.trans (h.1 n hn).2.symm
    by_cases hr : k = n
    · subst k
      simpa using (h.1 n hn).2.trans (h.1 n hn).1.symm
    have hn' : 1 ≤ n - 1 := by omega
    have e₁ := ih (n - 1) (by omega) (k - 1) hn' (by omega) (by omega)
    have e₂ := ih (n - 1) (by omega) k hn' hk (by omega)
    have i₁ : n - 1 + 1 - (k - 1) = n + 1 - k := by omega
    have i₂ : n - 1 + 1 - k = n + 1 - k - 1 := by omega
    rw [i₁] at e₁
    rw [i₂] at e₂
    rw [h.2 n k (by omega) (by omega),
      h.2 n (n + 1 - k) (by omega) (by omega), ← e₁, ← e₂]
    have hc : ((n + 1 - k : ℕ) : ℤ) = (n : ℤ) + 1 - (k : ℤ) := by omega
    rw [hc]
    ring

private theorem second_step {r : ℤ} {T : ℕ → ℕ → ℤ} (h : Source (-r) T)
    (n : ℕ) (hn : 2 ≤ n) :
    T (n + 1) 2 = 1 - r * ((n : ℤ) - 1) + (1 - r) * T n 2 := by
  rw [h.2 (n + 1) 2 (by omega) (by omega)]
  simp only [Nat.add_sub_cancel, Nat.reduceSub, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, (h.1 n (by omega)).1]
  ring

/-- Eliminating the intervening row makes the boundary-column forcing positive. -/
private theorem second_two_step {r : ℤ} {T : ℕ → ℕ → ℤ} (h : Source (-r) T)
    (n : ℕ) (hn : 2 ≤ n) :
    T (n + 2) 2 = (r - 1) ^ 2 * T n 2 +
      r * (r - 2) * (n : ℤ) + 2 - r ^ 2 := by
  rw [show n + 2 = (n + 1) + 1 by omega, second_step h _ (by omega),
    second_step h n hn]
  push_cast
  ring

private theorem second_even_positive {r : ℤ} {T : ℕ → ℕ → ℤ}
    (hr : 3 ≤ r) (h : Source (-r) T) (q : ℕ) : 0 < T (2 * q + 2) 2 := by
  induction q with
  | zero => simpa using (show (0 : ℤ) < T 2 2 by rw [(h.1 2 (by omega)).2]; omega)
  | succ q ih =>
    rw [show 2 * (q + 1) + 2 = (2 * q + 2) + 2 by omega,
      second_two_step h _ (by omega)]
    by_cases hq : q = 0
    · subst q
      norm_num only [mul_zero, zero_add, Nat.cast_ofNat]
      rw [(h.1 2 (by omega)).2]
      nlinarith [mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ r - 3 by omega)]
    · have hn : (4 : ℤ) ≤ (2 * q + 2 : ℕ) := by omega
      have hp : 0 ≤ r * (r - 2) := mul_nonneg (by omega) (by omega)
      have hf := mul_nonneg hp (show 0 ≤ ((2 * q + 2 : ℕ) : ℤ) - 4 by omega)
      have hs : 0 < (r - 1) ^ 2 * T (2 * q + 2) 2 :=
        mul_pos (sq_pos_of_pos (by omega)) ih
      nlinarith [mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ r - 3 by omega)]

private theorem coefficient_negative {r : ℤ} (hr : 3 ≤ r) {a : ℤ} (ha : 1 ≤ a) :
    -r * a + 1 < 0 := by
  have := mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ a - 1 by omega)
  nlinarith

private theorem next_interior_negative {r : ℤ} {T : ℕ → ℕ → ℤ}
    (hr : 3 ≤ r) (h : Source (-r) T) (n : ℕ)
    (hp : ∀ k, 1 ≤ k → k ≤ n → 0 < T n k)
    (k : ℕ) (hk : 1 < k) (hkn : k < n + 1) : T (n + 1) k < 0 := by
  rw [h.2 (n + 1) k hk hkn, Nat.add_sub_cancel]
  exact add_neg
    (mul_neg_of_neg_of_pos (coefficient_negative hr (by omega)) (hp _ (by omega) (by omega)))
    (mul_neg_of_neg_of_pos (coefficient_negative hr (by omega)) (hp _ (by omega) (by omega)))

private theorem positive_rows {r : ℤ} {T : ℕ → ℕ → ℤ}
    (hr : 3 ≤ r) (h : Source (-r) T) (q : ℕ) :
    ∀ k, 1 ≤ k → k ≤ 2 * q + 2 → 0 < T (2 * q + 2) k := by
  induction q with
  | zero =>
    intro k hk hkn
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl <;> norm_num [(h.1 2 (by omega)).1, (h.1 2 (by omega)).2]
  | succ q ih =>
    intro k hk hkn
    by_cases hl : k = 1
    · subst k
      rw [(h.1 _ (by omega)).1]
      omega
    by_cases hr' : k = 2 * (q + 1) + 2
    · subst k
      rw [(h.1 _ (by omega)).2]
      omega
    by_cases hs : k = 2
    · subst k
      exact second_even_positive hr h (q + 1)
    by_cases ht : k = 2 * (q + 1) + 1
    · rw [reflection h _ k (by omega) hk hkn]
      have : 2 * (q + 1) + 2 + 1 - k = 2 := by omega
      rw [this]
      exact second_even_positive hr h (q + 1)
    have hn₁ := next_interior_negative hr h (2 * q + 2) ih
      (k - 1) (by omega) (by omega)
    have hn₂ := next_interior_negative hr h (2 * q + 2) ih
      k (by omega) (by omega)
    rw [h.2 _ k (by omega) (by omega)]
    have hi : 2 * (q + 1) + 2 - 1 = 2 * q + 2 + 1 := by omega
    rw [hi]
    exact add_pos
      (mul_pos_of_neg_of_neg (coefficient_negative hr (by omega)) hn₁)
      (mul_pos_of_neg_of_neg (coefficient_negative hr (by omega)) hn₂)

/-- Every admissible triangle for an integer step -r, r ≥ 3, has strictly
positive entries throughout each positive even row. -/
theorem even_rows_positive (r : ℤ) (hr : 3 ≤ r) (T : ℕ → ℕ → ℤ)
    (h : Source (-r) T) (n : ℕ) (hn : 1 ≤ n) (he : Even n)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : 0 < T n k := by
  obtain ⟨q, hq⟩ := he
  have hq' : 1 ≤ q := by omega
  have hn' : n = 2 * (q - 1) + 2 := by omega
  rw [hn']
  exact positive_rows hr h (q - 1) k hk (by omega)

private theorem parameter_claim (r : ℤ) (hr : 3 ≤ r) : ParityPositivity (-r) := by
  refine ⟨source_exists _, ?_⟩
  intro T h n hn he k hk hkn
  exact le_of_lt (even_rows_positive r hr T h n hn he k hk hkn)

/-- The three original nonnegativity assertions, including existence and the
universal quantifier over all solutions of each source recurrence. -/
theorem result : claim := by
  exact ⟨parameter_claim 3 (by omega), parameter_claim 4 (by omega),
    parameter_claim 5 (by omega)⟩

#print axioms even_rows_positive
#print axioms result

end D5.S1.Recurrence.Algebraic.ChenChenParityPositivity
