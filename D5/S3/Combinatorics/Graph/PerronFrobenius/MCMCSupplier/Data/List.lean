/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Data/List
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Data/List
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LICENSE.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
import Mathlib.Tactic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.List.Basic
namespace List
open List
variable {α : Type*}
lemma exists_mem_split {l : List α} {x : α} (h : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  induction l with
  | nil     => cases h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h'
    ·
      exact ⟨[], ys, by simp only [List.nil_append]⟩
    · rcases ih h' with ⟨l₁, l₂, rfl⟩
      use y :: l₁, l₂
      simp only [List.cons_append]
variable {α : Type*} {l m : List α} {n : ℕ}
variable {α : Type*} [DecidableEq α]
def ContainsDup {α : Type*} [DecidableEq α] (l : List α) : Prop :=
  ∃ x, 2 ≤ l.count x
lemma nodup_iff_not_contains_dup {α : Type*} [DecidableEq α] {l : List α} :
    l.Nodup ↔ ¬l.ContainsDup := by
  rw [List.nodup_iff_count_le_one, List.ContainsDup, not_exists]
  constructor
  · intro h x
    specialize h x
    simp only [not_le]
    exact Nat.lt_of_le_of_lt h (Nat.lt_add_one 1)
  · intro h x
    specialize h x
    exact Nat.le_of_lt_succ (Nat.lt_of_not_le h)
variable {α : Type*} [DecidableEq α]
lemma idxOf_append_left {v : α} {l₁ l₂ : List α}
    (hv : v ∈ l₁) :
    List.idxOf v (l₁ ++ l₂) = List.idxOf v l₁ := by
  induction l₁ with
  | nil => cases hv
  | cons x xs ih =>
    by_cases h : v = x
    · simp only [h, cons_append, idxOf_cons_self]
    · have hvxs : v ∈ xs := by simpa [h] using hv
      dsimp only [cons_append, idxOf]
      rw [← cons_append]
      simp only [cons_append, findIdx_cons]
      congr! 1; exact congrFun (congrArg HAdd.hAdd (ih hvxs)) 1
lemma ne_nil_of_head?_eq_some {α : Type*} {l : List α} {x : α} (h : l.head? = some x) : l ≠ [] := by
  by_contra heq
  rw [heq] at h
  simp only [head?_nil, reduceCtorEq] at h
lemma idxOf_eq_idxOf_of_isPrefix {v : α} {l₁ l₂ : List α}
    (hpref : List.IsPrefix l₁ l₂) (hv : v ∈ l₁) :
    List.idxOf v l₂ = List.idxOf v l₁ := by
  rcases hpref with ⟨t, rfl⟩
  simpa using idxOf_append_left hv
namespace Nat
@[simp] lemma eq_of_le_zero {n : ℕ} (h : n ≤ 0) : n = 0 :=
  le_antisymm h (Nat.zero_le _)
end Nat
lemma get_idxOf_of_mem {l : List α} {x : α} (h : x ∈ l) :
  l.get ⟨idxOf x l, idxOf_lt_length_of_mem h⟩ = x := by
  simp [get_eq_getElem]
end List
