/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighTypes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighTypes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Classify bounded seven-point natural-valued functions with sum thirteen and square sum at most twenty-seven. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

/-! Internal scalar helper for the remaining symmetric slice analysis.
The classification follows from actual cardinality, first moment, and second
moment inequalities, without an external enumeration certificate. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighTypes

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

private def count (S : Finset V) (g : V → ℕ) (i : ℕ) : ℕ :=
  (S.filter fun x => g x = i).card

private theorem count_insert (g : V → ℕ) {S : Finset V} {a : V}
    (ha : a ∉ S) (i : ℕ) :
    count (insert a S) g i = count S g i + if g a = i then 1 else 0 := by
  by_cases hi : g a = i
  · simp [count, Finset.filter_insert, ha, hi]
  · simp [count, Finset.filter_insert, hi]

private theorem count_decompositions (S : Finset V) (g : V → ℕ)
    (hbound : ∀ x ∈ S, g x ≤ 3) :
    S.card = count S g 0 + count S g 1 + count S g 2 + count S g 3 ∧
    (∑ x ∈ S, g x) = count S g 1 + 2 * count S g 2 + 3 * count S g 3 ∧
    (∑ x ∈ S, (g x) ^ 2) =
      count S g 1 + 4 * count S g 2 + 9 * count S g 3 := by
  classical
  revert hbound
  induction S using Finset.induction_on with
  | empty =>
      intro _hbound
      simp [count]
  | @insert a S ha ih =>
      intro hbound
      have hb : ∀ x ∈ S, g x ≤ 3 := by
        intro x hx
        exact hbound x (Finset.mem_insert_of_mem hx)
      obtain ⟨hc, hs, hq⟩ := ih hb
      have hga : g a ≤ 3 := hbound a (Finset.mem_insert_self _ _)
      have hcases : g a = 0 ∨ g a = 1 ∨ g a = 2 ∨ g a = 3 := by omega
      refine ⟨?_, ?_, ?_⟩
      all_goals
        rcases hcases with hga | hga | hga | hga
        all_goals
          simp [count_insert g ha, ha, hga] <;> omega

/-- A seven-point function with sum thirteen and square sum at most twenty-seven
has no zero values and has precisely one of the two stated high-neighbor types. -/
theorem high_type_classification (S : Finset V) (g : V → ℕ)
    (hcard : S.card = 7)
    (hsum : (∑ x ∈ S, g x) = 13)
    (hbound : ∀ x ∈ S, g x ≤ 3)
    (hsquare : (∑ x ∈ S, (g x) ^ 2) ≤ 27) :
    (S.filter fun x => g x = 0).card = 0 ∧
    (((S.filter fun x => g x = 1).card,
      (S.filter fun x => g x = 2).card,
      (S.filter fun x => g x = 3).card) = (1, 6, 0) ∨
     ((S.filter fun x => g x = 1).card,
      (S.filter fun x => g x = 2).card,
      (S.filter fun x => g x = 3).card) = (2, 4, 1)) ∧
    ∀ x ∈ S, g x ≠ 0 := by
  classical
  obtain ⟨hc, hs, hq⟩ := count_decompositions S g hbound
  have hclass : count S g 0 = 0 ∧
      ((count S g 1 = 1 ∧ count S g 2 = 6 ∧ count S g 3 = 0) ∨
       (count S g 1 = 2 ∧ count S g 2 = 4 ∧ count S g 3 = 1)) := by
    have h3 : count S g 3 = 0 ∨ count S g 3 = 1 := by omega
    rcases h3 with h3 | h3
    · refine ⟨?_, Or.inl ⟨?_, ?_, h3⟩⟩ <;> omega
    · refine ⟨?_, Or.inr ⟨?_, ?_, h3⟩⟩ <;> omega
  have htuple :
      (count S g 1, count S g 2, count S g 3) = (1, 6, 0) ∨
      (count S g 1, count S g 2, count S g 3) = (2, 4, 1) := by
    rcases hclass.2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left
      simp only [h1, h2, h3]
    · right
      simp only [h1, h2, h3]
  refine ⟨hclass.1, htuple, ?_⟩
  intro x hx hx0
  have hxF : x ∈ S.filter (fun y => g y = 0) := Finset.mem_filter.mpr ⟨hx, hx0⟩
  have hpos : 0 < (S.filter fun y => g y = 0).card := Finset.card_pos.mpr ⟨x, hxF⟩
  have hzero : (S.filter fun y => g y = 0).card = 0 := hclass.1
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighTypes
