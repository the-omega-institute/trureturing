/- GID: D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs
   mirror-E: none(waiver:definitions-for-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kasel stage schemes, dyadic blocks, validity and normalization
     at horizon four to the m. -/

import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.KaselDisplacementLadderDefs

/-- Kasel's dyadic block index: for v ≥ 2, the unique k with 2^(k-1) < v ≤ 2^k. -/
def block (v : ℕ) : ℕ := Nat.clog 2 v

/-- S_A ∩ [1, 4^m]: values in dyadic blocks (2^(k-1), 2^k] with k ≥ 2 even. -/
def SA (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (4 ^ m)).filter (fun v => 2 ≤ block v ∧ Even (block v))

/-- Position order of the concatenation: stage first, then the fibre order. -/
def lexLess (s r : ℕ → ℕ) (a b : ℕ) : Prop :=
  s a < s b ∨ (s a = s b ∧ r a < r b)

/-- A valid scheme on X: within each fibre r is injective (a linear fibre order), and
 the concatenation contains no monotone three-term arithmetic progression. -/
def Valid (X : Finset ℕ) (s r : ℕ → ℕ) : Prop :=
  (∀ a ∈ X, ∀ b ∈ X, s a = s b → r a = r b → a = b) ∧
  ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x < y → y < z → x + z = 2 * y →
    ¬ (lexLess s r x y ∧ lexLess s r y z) ∧ ¬ (lexLess s r z y ∧ lexLess s r y x)

/-- Kasel's normalization δ ≥ 0, i.e. s v ≥ block v / 2. -/
def Normalized (X : Finset ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ v ∈ X, block v / 2 ≤ s v

/-- S_A ∩ [1, 16]. -/
def distinguished : Finset ℕ := {3, 4, 9, 10, 11, 12, 13, 14, 15, 16}

lemma block_eq_of_pow_pred_lt_le_pow {k v : ℕ} (hk : 1 ≤ k)
    (hlo : 2 ^ (k - 1) < v) (hhi : v ≤ 2 ^ k) : block v = k := by
  apply Nat.le_antisymm
  · exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hhi
  · have hlt : k - 1 < block v :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hlo
    omega


lemma distinguished_subset {m : ℕ} (hm : 2 ≤ m) : distinguished ⊆ SA m := by
  have hpow : 16 ≤ 4 ^ m := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 4) hm
    norm_num at h ⊢
    exact h
  intro v hv
  simp only [distinguished, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [SA, Finset.mem_filter, Finset.mem_Icc]
  all_goals norm_num [block, Nat.clog]
  all_goals omega

end D5.S3.Combinatorics.Permutation.KaselDisplacementLadderDefs
