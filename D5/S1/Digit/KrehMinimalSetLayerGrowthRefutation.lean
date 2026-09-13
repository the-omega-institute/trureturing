/- GID: D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation
   generality: G
   mirror-B: D5/B/S1/Digit/KrehMinimalSetLayerGrowthRefutation
   mirror-E: none(waiver:symbolic-refutation-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Defs, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: An infinite decimal-subsequence set has minimal-layer sizes 1, 2, 1, 1, forever. -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Card

namespace D5.S1.Digit.KrehMinimalSetLayerGrowthRefutation

/-- The printed decimal digits of `a` occur in order among those of `b`. -/
def digitSubseq (a b : ℕ) : Prop :=
  ((Nat.digits 10 a).reverse).Sublist ((Nat.digits 10 b).reverse)

/-- The elements of `M` minimal under decimal-digit subsequence. -/
def minimal (M : Set ℕ) : Set ℕ :=
  {a | a ∈ M ∧ ∀ b ∈ M, digitSubseq b a → b = a}

/-- Successively remove the current minimal elements. -/
def peel (M : Set ℕ) : ℕ → Set ℕ
  | 0 => M
  | k + 1 => peel M k \ minimal (peel M k)

/-- The number of minimal elements at layer `k`. -/
noncomputable def eta (M : Set ℕ) (k : ℕ) : ℕ :=
  (minimal (peel M k)).ncard

/-- The divergent-layer assertion from the second sentence of Kreh's Conjecture 18. -/
def claim : Prop :=
  ∀ M : Set ℕ, (∀ n ∈ M, 0 < n) → M.Infinite → eta M 0 < eta M 1 →
    ∀ B : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → B ≤ eta M k

private def u (j : ℕ) : ℕ := 110 * 10 ^ j

private def witness : Set ℕ :=
  {1, 10, 11} ∪ Set.range u

end D5.S1.Digit.KrehMinimalSetLayerGrowthRefutation
