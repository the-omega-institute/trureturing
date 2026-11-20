/- GID: D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/ChenChenRealStepSigns
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For real r ≥ 3 and step -r, even rows are positive and odd-row interiors negative. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#2 and #3)
escape_witness: second_even_positive (eliminating the odd row gives
  T(n+2,2) = (r-1)² T(n,2) + r(r-2)n + 2 - r², whose forcing term is positive for n ≥ 2 and
  real r ≥ 3, so the second column is positive in every even row) and positive_rows (from a
  positive even row both recursion coefficients are negative at every interior position of the
  next odd row, making it negative, and both products are then positive in the following even
  row).
proof_shape:
  claim: source definition; consumer: result.
  second_step, second_two_step: bind-only helpers (instantiation of Source, push_cast, ring);
    consumers: second_two_step, second_even_positive.
  second_even_positive: content; consumer: positive_rows.
  coefficient_negative: bind-only helper (nlinarith); consumers: next_interior_negative,
    positive_rows.
  next_interior_negative: content (sign propagation from a positive row); consumers:
    positive_rows, result.
  positive_rows: content; consumer: result.
  result: content only through positive_rows and next_interior_negative; existence is
    ChenChenRealStepRowSums.source_exists.
Direct frozen dependencies: none frozen yet; D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums
  (Source, reflection, source_exists) is frozen in the same delivery.
Search record (§3.1): D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.even_rows_positive
  is the integer-step special case over ℤ; its helpers are private and stated for
  Source (m : ℤ) (T : ℕ → ℕ → ℤ), so they cannot be applied at a real step, and the module has
  no odd-row statement. The sign argument here is the same two-step propagation, carried out
  over ℝ.
-/

import D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums

/-! # Signs of the real-step Eulerian triangle at steps `-r`, `r ≥ 3`

For real `r ≥ 3` and every solution `T` of the step-`(-r)` recursion, every entry of a positive
even row is positive and every interior entry of an odd row `n ≥ 3` is negative. In particular
the second column is positive in every even row `n ≥ 2`.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.ChenChenRealStepSigns

open D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums

private theorem second_step {r : ℝ} {T : ℕ → ℕ → ℝ} (h : Source (-r) T) (n : ℕ) (hn : 2 ≤ n) :
    T (n + 1) 2 = 1 - r * ((n : ℝ) - 1) + (1 - r) * T n 2 := by
  rw [h.2 (n + 1) 2 (by omega) (by omega)]
  simp only [Nat.add_sub_cancel, Nat.reduceSub, (h.1 n (by omega)).1]
  push_cast
  ring

private theorem second_two_step {r : ℝ} {T : ℕ → ℕ → ℝ} (h : Source (-r) T) (n : ℕ)
    (hn : 2 ≤ n) :
    T (n + 2) 2 = (r - 1) ^ 2 * T n 2 + r * (r - 2) * (n : ℝ) + 2 - r ^ 2 := by
  rw [show n + 2 = (n + 1) + 1 by omega, second_step h _ (by omega), second_step h n hn]
  push_cast
  ring

/-- For real `r ≥ 3`, the second column is positive in every even row `n ≥ 2`. -/
theorem second_even_positive {r : ℝ} (hr : 3 ≤ r) {T : ℕ → ℕ → ℝ} (h : Source (-r) T)
    {n : ℕ} (hn : 2 ≤ n) (he : Even n) : 0 < T n 2 := by
  obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q + 2 := by
    obtain ⟨p, hp⟩ := he; exact ⟨p - 1, by omega⟩
  clear hn he
  induction q with
  | zero => rw [(h.1 2 (by omega)).2]; norm_num
  | succ q ih =>
    rw [show 2 * (q + 1) + 2 = (2 * q + 2) + 2 by omega, second_two_step h _ (by omega)]
    have hr0 : (0 : ℝ) ≤ r := by linarith
    have hs : 0 < (r - 1) ^ 2 * T (2 * q + 2) 2 := mul_pos (by nlinarith) ih
    have hq : (4 : ℝ) ≤ ((2 * q + 2 : ℕ) : ℝ) ∨ q = 0 := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exact Or.inr h0
      · left; have : (2 : ℝ) ≤ (q : ℝ) + 1 := by
          have : (1 : ℝ) ≤ q := by exact_mod_cast h0
          linarith
        push_cast; linarith
    rcases hq with hq | rfl
    · have hp : 0 ≤ r * (r - 2) := mul_nonneg hr0 (by linarith)
      have hf := mul_nonneg hp (show (0 : ℝ) ≤ ((2 * q + 2 : ℕ) : ℝ) - 4 by linarith)
      nlinarith [mul_nonneg hr0 (show (0 : ℝ) ≤ r - 3 by linarith)]
    · norm_num
      rw [(h.1 2 (by omega)).2]
      nlinarith [mul_nonneg hr0 (show (0 : ℝ) ≤ r - 3 by linarith)]

private theorem coefficient_negative {r : ℝ} (hr : 3 ≤ r) {a : ℝ} (ha : 1 ≤ a) :
    -r * a + 1 < 0 := by
  nlinarith

private theorem next_interior_negative {r : ℝ} (hr : 3 ≤ r) {T : ℕ → ℕ → ℝ}
    (h : Source (-r) T) (n : ℕ) (hp : ∀ k, 1 ≤ k → k ≤ n → 0 < T n k)
    (k : ℕ) (hk : 1 < k) (hkn : k < n + 1) : T (n + 1) k < 0 := by
  rw [h.2 (n + 1) k hk hkn, Nat.add_sub_cancel]
  have c1 : -r * (((n + 1 : ℕ) : ℝ) - (k : ℝ)) + 1 < 0 := by
    apply coefficient_negative hr
    have : (k : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hkn
    linarith
  have c2 : -r * ((k : ℝ) - 1) + 1 < 0 := by
    apply coefficient_negative hr
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  exact add_neg (mul_neg_of_neg_of_pos c1 (hp _ (by omega) (by omega)))
    (mul_neg_of_neg_of_pos c2 (hp _ (by omega) (by omega)))

private theorem positive_rows {r : ℝ} (hr : 3 ≤ r) {T : ℕ → ℕ → ℝ} (h : Source (-r) T)
    (q : ℕ) : ∀ k, 1 ≤ k → k ≤ 2 * q + 2 → 0 < T (2 * q + 2) k := by
  induction q with
  | zero =>
    intro k hk hkn
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl <;> norm_num [(h.1 2 (by omega)).1, (h.1 2 (by omega)).2]
  | succ q ih =>
    intro k hk hkn
    have hev : Even (2 * (q + 1) + 2) := ⟨q + 2, by ring⟩
    by_cases hl : k = 1
    · subst k; rw [(h.1 _ (by omega)).1]; norm_num
    by_cases hr' : k = 2 * (q + 1) + 2
    · subst k; rw [(h.1 _ (by omega)).2]; norm_num
    by_cases hs : k = 2
    · subst k; exact second_even_positive hr h (by omega) hev
    by_cases ht : k = 2 * (q + 1) + 1
    · rw [reflection h _ k (by omega) hk hkn,
        show 2 * (q + 1) + 2 + 1 - k = 2 by omega]
      exact second_even_positive hr h (by omega) hev
    have hn₁ := next_interior_negative hr h (2 * q + 2) ih (k - 1) (by omega) (by omega)
    have hn₂ := next_interior_negative hr h (2 * q + 2) ih k (by omega) (by omega)
    rw [h.2 _ k (by omega) (by omega), show 2 * (q + 1) + 2 - 1 = 2 * q + 2 + 1 by omega]
    have c1 : -r * (((2 * (q + 1) + 2 : ℕ) : ℝ) - (k : ℝ)) + 1 < 0 := by
      apply coefficient_negative hr
      have : (k : ℝ) + 1 ≤ ((2 * (q + 1) + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : k + 1 ≤ 2 * (q + 1) + 2)
      linarith
    have c2 : -r * ((k : ℝ) - 1) + 1 < 0 := by
      apply coefficient_negative hr
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
      linarith
    exact add_pos (mul_pos_of_neg_of_neg c1 hn₁) (mul_pos_of_neg_of_neg c2 hn₂)

/-- Existence, positivity of positive even rows and negativity of odd-row interiors, for
every real `r ≥ 3` and every solution of the step-`(-r)` recursion. -/
def claim : Prop :=
  ∀ r : ℝ, 3 ≤ r → (∃ T, Source (-r) T) ∧ ∀ T : ℕ → ℕ → ℝ, Source (-r) T →
    (∀ n, 1 ≤ n → Even n → ∀ k, 1 ≤ k → k ≤ n → 0 < T n k) ∧
    (∀ n, 3 ≤ n → Odd n → ∀ k, 1 < k → k < n → T n k < 0)

/-- The sign pattern holds. -/
theorem result : claim := by
  intro r hr
  refine ⟨source_exists (-r), fun T h => ?_⟩
  have heven : ∀ n, 1 ≤ n → Even n → ∀ k, 1 ≤ k → k ≤ n → 0 < T n k := by
    intro n hn he k hk hkn
    obtain ⟨q, hq⟩ := he
    rw [show n = 2 * (q - 1) + 2 by omega]
    exact positive_rows hr h (q - 1) k hk (by omega)
  refine ⟨heven, fun n hn ho k hk hkn => ?_⟩
  obtain ⟨q, hq⟩ := ho
  rw [show n = (2 * q) + 1 by omega]
  exact next_interior_negative hr h (2 * q)
    (heven (2 * q) (by omega) ⟨q, by ring⟩) k hk (by omega)

end D5.S1.Recurrence.Algebraic.ChenChenRealStepSigns
