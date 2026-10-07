/- GID: D5/S1/Words/Palindromes/FridPrefix/PalindromicLength
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/PalindromicLength
   mirror-E: none(waiver:finite-word-factorisation)
   anchors: []
   utility: none
   digest: Palindromic factorisations give subadditivity and a one-letter length bound. -/

/-
proof_shape: content (pl_one_letter_lipschitz).
escape_witness: deletion of a last palindrome, requiring a new two-factor split.
admission_basis: escape-witness.
Direct frozen dependencies: none; remaining dependencies are pinned Mathlib or this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.List.Palindrome
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Ring.Abs

namespace D5.S1.Words.FridPrefix

/-- Exactly `k` nonempty palindrome factors concatenate to `w`. -/
def PalFactors {α : Type*} (w : List α) (k : ℕ) : Prop :=
  ∃ ps : List (List α), ps.flatten = w ∧ ps.length = k ∧
    ∀ p ∈ ps, p ≠ [] ∧ List.Palindrome p

/-- The minimum number of nonempty palindrome factors. -/
noncomputable def PL {α : Type*} (w : List α) : ℕ := by
  classical
  have he : ∃ k, PalFactors w k := by
    refine ⟨w.length, w.map (fun a => [a]), ?_, by simp, ?_⟩
    · induction w with
      | nil => rfl
      | cons a w ih => simpa using congrArg (List.cons a) ih
    · intro p hp
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨by simp, List.Palindrome.singleton a⟩
  exact Nat.find he

/-- Deleting a letter from a last palindrome requires at most one additional factor. -/
theorem pl_one_letter_lipschitz {α : Type*} (w : List α) (a : α) :
    |(PL (w ++ [a]) : ℤ) - (PL w : ℤ)| ≤ 1 := by
  classical
  have append_le (u v : List α) : PL (u ++ v) ≤ PL u + PL v := by
    classical
    obtain ⟨ps, hps, hlenps, hp⟩ : PalFactors u (PL u) := by
      unfold PL
      exact Nat.find_spec _
    obtain ⟨qs, hqs, hlenqs, hq⟩ : PalFactors v (PL v) := by
      unfold PL
      exact Nat.find_spec _
    apply Nat.find_le (show PalFactors (u ++ v) (PL u + PL v) from ?_)
    refine ⟨ps ++ qs, by simp [hps, hqs], by simp [hlenps, hlenqs], ?_⟩
    intro p h
    rcases List.mem_append.mp h with h | h
    · exact hp p h
    · exact hq p h
  have pal_le {v : List α} (hv : List.Palindrome v) : PL v ≤ 1 := by
    by_cases he : v = []
    · subst v
      have hn : PL ([] : List α) ≤ 0 :=
        Nat.find_le (show PalFactors ([] : List α) 0 from ⟨[], rfl, rfl, by simp⟩)
      omega
    · exact Nat.find_le (show PalFactors v 1 from
        ⟨[v], by simp, rfl, by simpa using And.intro he hv⟩)
  have drop_pal {v : List α} (hv : List.Palindrome v) : PL v.dropLast ≤ 2 := by
    cases hv with
    | nil =>
      have hn : PL ([] : List α) ≤ 0 :=
        Nat.find_le (show PalFactors ([] : List α) 0 from ⟨[], rfl, rfl, by simp⟩)
      simpa only [List.dropLast_nil] using hn.trans (by omega)
    | singleton a =>
      have hn : PL ([] : List α) ≤ 0 :=
        Nat.find_le (show PalFactors ([] : List α) 0 from ⟨[], rfl, rfl, by simp⟩)
      simpa only [List.dropLast_singleton] using hn.trans (by omega)
    | @cons_concat a l hl =>
      rw [← List.cons_append, List.dropLast_concat]
      have hb := append_le [a] l
      have hs := pal_le (List.Palindrome.singleton a)
      have hm := pal_le hl
      change PL ([a] ++ _) ≤ 2
      omega
  have drop_le (v : List α) : PL v.dropLast ≤ PL v + 1 := by
    obtain ⟨ps, hps, hlen, hp⟩ : PalFactors v (PL v) := by
      unfold PL
      exact Nat.find_spec _
    cases ps using List.reverseRecOn with
    | nil =>
      have he : v = [] := hps.symm
      subst v
      have hn : PL ([] : List α) ≤ 0 :=
        Nat.find_le (show PalFactors ([] : List α) 0 from ⟨[], rfl, rfl, by simp⟩)
      change PL ([] : List α) ≤ PL ([] : List α) + 1
      omega
    | append_singleton qs p ih =>
      have hpal := hp p (by simp)
      have hq : PL qs.flatten ≤ qs.length := Nat.find_le
        (show PalFactors qs.flatten qs.length from
          ⟨qs, rfl, rfl, fun q hq => hp q (by simp [hq])⟩)
      have hr := drop_pal hpal.2
      have hdp : v.dropLast = qs.flatten ++ p.dropLast := by
        rw [← hps, List.flatten_append, List.flatten_singleton,
          List.dropLast_append_of_ne_nil hpal.1]
      rw [hdp]
      have hb := append_le qs.flatten p.dropLast
      simp only [List.length_append, List.length_singleton] at hlen
      omega
  have hu := append_le w [a]
  have hs := pal_le (List.Palindrome.singleton a)
  have hl := drop_le (w ++ [a])
  simp only [List.dropLast_concat] at hl
  rw [abs_le]
  constructor <;> omega

end D5.S1.Words.FridPrefix
