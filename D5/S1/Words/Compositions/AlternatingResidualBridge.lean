/- GID: D5/S1/Words/Compositions/AlternatingResidualBridge
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/AlternatingResidualBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Blocked alternating words correspond to interlaced residual pairs. -/

import D5.S1.Words.Compositions.ResidualPermutationSign
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace D5.S1.Words.Compositions.AlternatingResidualBridge

open ResidualPermutationSign

/-- Every height, including the initial and final height, is nonnegative. -/
def Good (h : ℤ) : List ℤ → Prop
  | [] => 0 ≤ h
  | x :: w => 0 ≤ h ∧ Good (h + x) w

/-- No complete disjoint position pair permits both orders at its starting height. -/
def Unswappable (h : ℤ) : List ℤ → Prop
  | x :: y :: w => ¬ (0 ≤ h + x ∧ 0 ≤ h + y) ∧ Unswappable (h + x + y) w
  | _ => True

/-- Expand each pair as a positive step followed by a negative step, then append zero. -/
def alternating : List (ℕ × ℕ) → List ℤ
  | [] => [0]
  | (a, b) :: l => (a : ℤ) :: -(b : ℤ) :: alternating l

private def firstSum (l : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  ((l.take k).map Prod.fst).sum

private def secondSum (l : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  ((l.take k).map Prod.snd).sum

private theorem alternating_rule (l : List (ℕ × ℕ)) (h : ℤ) :
    Good h (alternating l) ∧ Unswappable h (alternating l) ↔
      0 ≤ h ∧ ∀ k < l.length,
        h + (firstSum l k : ℤ) < (secondSum l (k + 1) : ℤ) ∧
        (secondSum l (k + 1) : ℤ) ≤ h + (firstSum l (k + 1) : ℤ) := by
  induction l generalizing h with
  | nil => simp [alternating, Good, Unswappable]
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    constructor
    · rintro ⟨⟨hh, ha, hg⟩, hn, hu⟩
      obtain ⟨ht, hi⟩ := (ih (h + a + - (b : ℤ))).mp ⟨hg, hu⟩
      refine ⟨hh, fun k hk => ?_⟩
      cases k with
      | zero =>
        simp only [firstSum, secondSum, List.take_zero, List.take_succ_cons,
          List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
          Nat.cast_zero, add_zero]
        constructor <;> omega
      | succ k =>
        have hk' : k < l.length := by simpa using hk
        have hi' := hi k hk'
        simp only [firstSum, secondSum, List.take_succ_cons, List.map_cons,
          List.sum_cons, Nat.cast_add] at *
        constructor <;> omega
    · rintro ⟨hh, hi⟩
      have hzero := hi 0 (by simp)
      simp only [firstSum, secondSum, List.take_zero, List.take_succ_cons,
        List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
        Nat.cast_zero, add_zero] at hzero
      have ha : 0 ≤ h + (a : ℤ) := by omega
      have ht : 0 ≤ h + (a : ℤ) + -(b : ℤ) := by omega
      have htail : ∀ k < l.length,
          h + a + -(b : ℤ) + (firstSum l k : ℤ) < (secondSum l (k + 1) : ℤ) ∧
          (secondSum l (k + 1) : ℤ) ≤
            h + a + -(b : ℤ) + (firstSum l (k + 1) : ℤ) := by
        intro k hk
        have hs := hi (k + 1) (by simpa using hk)
        simp only [firstSum, secondSum, List.take_succ_cons, List.map_cons,
          List.sum_cons, Nat.cast_add] at *
        constructor <;> omega
      obtain ⟨hg, hu⟩ := (ih (h + a + -(b : ℤ))).mpr ⟨ht, htail⟩
      exact ⟨⟨hh, ha, hg⟩, by omega, hu⟩

/-- The zero-based permutation values are shifted to the positive integers. -/
def encode {m : ℕ} (a b : Equiv.Perm (Fin m)) : List ℤ :=
  alternating (List.ofFn fun i => ((a i).val + 1, (b i).val + 1))

/-- On explicitly alternating words, the blocked prefix rule is exactly the residual condition. -/
theorem encode_rule_iff {m : ℕ} (a b : Equiv.Perm (Fin m)) :
    Good 0 (encode a b) ∧ Unswappable 0 (encode a b) ↔ InResidual a b := by
  rw [encode, alternating_rule]
  simp only [le_refl, true_and, List.length_ofFn, zero_add]
  have hfirst (k : ℕ) :
      firstSum (List.ofFn fun i => ((a i).val + 1, (b i).val + 1)) k =
        prefixSum a k := by
    simp only [firstSum, List.map_take, List.map_ofFn, List.sum_take_ofFn, prefixSum]
    rfl
  have hsecond (k : ℕ) :
      secondSum (List.ofFn fun i => ((a i).val + 1, (b i).val + 1)) k =
        prefixSum b k := by
    simp only [secondSum, List.map_take, List.map_ofFn, List.sum_take_ofFn, prefixSum]
    rfl
  simp only [hfirst, hsecond, Nat.cast_lt, Nat.cast_le, InResidual]
  constructor
  · intro h i; exact h i.val i.isLt
  · intro h k hk; exact h ⟨k, hk⟩

end D5.S1.Words.Compositions.AlternatingResidualBridge
