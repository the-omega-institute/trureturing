/- GID: D5/S1/Recurrence/Algebraic/ChenChenIntegerStepCriterion
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/ChenChenIntegerStepCriterion
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For integer m, positive even rows are nonnegative iff m ≤ -3 or m ≥ 0, then positive. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#4)
escape_witness: all_rows_positive (for a nonnegative step both recursion coefficients are at
  least one, so every entry of every row is positive by induction on rows); the remaining
  integer steps -1 and -2 fail at T(4,2) = 2m² + 6m + 3 = -1, and steps m ≤ -3 are
  ChenChenRealStepSigns.result.
proof_shape:
  EvenRowsNonneg, EvenRowsPos, claim: source definitions; consumer: result.
  all_rows_positive: content; consumer: result.
  entry_four_two: bind-only helper (two instantiations of Source, ring); consumer: result.
  result: content through all_rows_positive and the sign theorem
    ChenChenRealStepSigns.result; the failing steps use source_exists and entry_four_two.
Direct frozen dependencies: none frozen yet; D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums
  (Source, source_exists) and D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns (result) are
  frozen in the same delivery.
Search record (§3.1): ChenChenParityPositivity proves positivity for integer steps m ≤ -3
  only; no D5 declaration treats nonnegative steps or the failure at m = -1, -2.
-/

import D5.S1.Recurrence.Algebraic.ChenChenRealStepSigns

/-! # Which integer steps give nonnegative even rows

For an integer step `m`, every positive even row of the step-`m` Eulerian triangle is entrywise
nonnegative exactly when `m ≤ -3` or `m ≥ 0`, and for these steps the even rows are strictly
positive. Nonnegative steps make every row positive, steps `m ≤ -3` are covered by the sign
theorem, and the steps `-1, -2` fail at `T(4,2) = -1`.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.ChenChenIntegerStepCriterion

open D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums

/-- Every positive even row of every solution is entrywise nonnegative. -/
def EvenRowsNonneg (m : ℝ) : Prop :=
  ∀ T : ℕ → ℕ → ℝ, Source m T → ∀ n, 1 ≤ n → Even n → ∀ k, 1 ≤ k → k ≤ n → 0 ≤ T n k

/-- Every positive even row of every solution is entrywise positive. -/
def EvenRowsPos (m : ℝ) : Prop :=
  ∀ T : ℕ → ℕ → ℝ, Source m T → ∀ n, 1 ≤ n → Even n → ∀ k, 1 ≤ k → k ≤ n → 0 < T n k

/-- The integer-step criterion for nonnegative even rows, with strict positivity. -/
def claim : Prop :=
  ∀ m : ℤ, (EvenRowsNonneg m ↔ (m ≤ -3 ∨ 0 ≤ m)) ∧ ((m ≤ -3 ∨ 0 ≤ m) → EvenRowsPos m)

/-- For a nonnegative step every entry of every row is positive. -/
private theorem all_rows_positive {m : ℝ} (hm : 0 ≤ m) {T : ℕ → ℕ → ℝ} (h : Source m T) :
    ∀ n, 1 ≤ n → ∀ k, 1 ≤ k → k ≤ n → 0 < T n k := by
  intro n
  induction n with
  | zero => intro h0; omega
  | succ n ih =>
    intro _ k hk hkn
    by_cases h1 : k = 1
    · subst h1; rw [(h.1 _ (by omega)).1]; norm_num
    by_cases h2 : k = n + 1
    · subst h2; rw [(h.1 _ (by omega)).2]; norm_num
    rw [h.2 (n + 1) k (by omega) (by omega), Nat.add_sub_cancel]
    have c1 : 0 < m * (((n + 1 : ℕ) : ℝ) - (k : ℝ)) + 1 := by
      have : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hkn
      nlinarith
    have c2 : 0 < m * ((k : ℝ) - 1) + 1 := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    exact add_pos (mul_pos c1 (ih (by omega) _ (by omega) (by omega)))
      (mul_pos c2 (ih (by omega) _ (by omega) (by omega)))

/-- The entry `T(4,2)` of every solution equals `2m + 1 + 2(m+1)²`. -/
private theorem entry_four_two {m : ℝ} {T : ℕ → ℕ → ℝ} (h : Source m T) :
    T 4 2 = 2 * m + 1 + 2 * (m + 1) ^ 2 := by
  have h3 : T 3 2 = 2 * (m + 1) := by
    rw [h.2 3 2 (by omega) (by omega)]
    simp only [show 3 - 1 = 2 by rfl, show 2 - 1 = 1 by rfl, (h.1 2 (by omega)).1,
      (h.1 2 (by omega)).2]
    push_cast; ring
  rw [h.2 4 2 (by omega) (by omega)]
  simp only [show 4 - 1 = 3 by rfl, show 2 - 1 = 1 by rfl, (h.1 3 (by omega)).1, h3]
  push_cast; ring

/-- The criterion holds for every integer step. -/
theorem result : claim := by
  intro m
  have hpos : (m ≤ -3 ∨ 0 ≤ m) → EvenRowsPos m := by
    rintro (hm | hm) T h n hn he k hk hkn
    · have hr : (3 : ℝ) ≤ -(m : ℝ) := by
        have : (m : ℝ) ≤ -3 := by exact_mod_cast hm
        linarith
      have h' : Source (-(-(m : ℝ))) T := by rwa [neg_neg]
      exact ((D5.S1.Recurrence.Algebraic.ChenChenRealStepSigns.result _ hr).2 T h').1
        n hn he k hk hkn
    · exact all_rows_positive (by exact_mod_cast hm) h n hn k hk hkn
  refine ⟨⟨fun hnn => ?_, fun hm T h n hn he k hk hkn => (hpos hm T h n hn he k hk hkn).le⟩,
    hpos⟩
  by_contra hm
  have hm' : m = -1 ∨ m = -2 := by omega
  obtain ⟨T, h⟩ := source_exists (m : ℝ)
  have h42 := hnn T h 4 (by omega) ⟨2, rfl⟩ 2 (by omega) (by omega)
  rw [entry_four_two h] at h42
  rcases hm' with rfl | rfl <;> norm_num at h42

end D5.S1.Recurrence.Algebraic.ChenChenIntegerStepCriterion
