/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/MultisetLex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/MultisetLex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lexicographic comparison of sorted dip multisets under common addition. -/

/-
admission_basis: escape-witness (sort_add_lex_iff)
escape_witness: sort_add_lex_iff
Direct frozen dependencies: none.
sort_add_lex_iff: proof_shape: content; escape_witness: sort_add_lex_iff; Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/

import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Lex

namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.MultisetLex
open List Multiset
private theorem lex_orderedInsert (a : ℕ) {l m : List ℕ} (h : List.Lex (· < ·) l m) :
    List.Lex (· < ·) (l.orderedInsert (· ≥ ·) a) (m.orderedInsert (· ≥ ·) a) := by
  induction h with
  | @nil b m =>
    by_cases hab : a ≥ b
    · simp only [List.orderedInsert_nil,List.orderedInsert_cons,ite_eq_left hab]
      exact .cons .nil
    · simp only [List.orderedInsert_nil,List.orderedInsert_cons,ite_eq_right hab]
      exact .rel (by omega)
  | @rel x l y m hxy =>
    by_cases hay : a ≥ y
    · have hax : a ≥ x := by omega
      simp only [List.orderedInsert_cons,ite_eq_left hay,ite_eq_left hax]
      exact .cons (.rel hxy)
    · by_cases hax : a ≥ x
      · simp only [List.orderedInsert_cons,ite_eq_right hay,ite_eq_left hax]
        exact .rel (by omega)
      · simp only [List.orderedInsert_cons,ite_eq_right hay,ite_eq_right hax]
        exact .rel hxy
  | @cons x l m h ih =>
    by_cases hax : a ≥ x
    · simp only [List.orderedInsert_cons,ite_eq_left hax]
      exact .cons (.cons h)
    · simp only [List.orderedInsert_cons,ite_eq_right hax]
      exact .cons ih
private theorem lex_orderedInsert_iff (a : ℕ) (l m : List ℕ) :
    List.Lex (· < ·) (l.orderedInsert (· ≥ ·) a) (m.orderedInsert (· ≥ ·) a) ↔
      List.Lex (· < ·) l m := by
  constructor
  · intro h
    rcases lt_trichotomy l m with hlt | heq | hgt
    · exact hlt
    · subst m
      exact (List.lex_irrefl Nat.lt_irrefl _ h).elim
    · exact (asymm h (lex_orderedInsert a hgt)).elim
  · exact lex_orderedInsert a
private theorem sort_cons_orderedInsert (a : ℕ) (s : Multiset ℕ) :
    (a ::ₘ s).sort (· ≥ ·) = (s.sort (· ≥ ·)).orderedInsert (· ≥ ·) a := by
  obtain ⟨l, hl⟩ := Quotient.exists_rep s
  subst s
  change Multiset.sort ((a :: l : List ℕ) : Multiset ℕ) (· ≥ ·) =
    (Multiset.sort (l : Multiset ℕ) (· ≥ ·)).orderedInsert (· ≥ ·) a
  simpa only [Multiset.coe_sort, List.mergeSort_eq_insertionSort] using
    (List.insertionSort_cons (r := (· ≥ ·)) a l)
theorem sort_add_lex_iff (s t u : Multiset ℕ) :
    List.Lex (· < ·) ((s+u).sort (· ≥ ·)) ((t+u).sort (· ≥ ·)) ↔
      List.Lex (· < ·) (s.sort (· ≥ ·)) (t.sort (· ≥ ·)) := by
  induction u using Multiset.induction_on with
  | empty => simp
  | @cons a u ih =>
    rw [Multiset.add_cons,Multiset.add_cons,sort_cons_orderedInsert,sort_cons_orderedInsert,
      lex_orderedInsert_iff,ih]
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.MultisetLex
