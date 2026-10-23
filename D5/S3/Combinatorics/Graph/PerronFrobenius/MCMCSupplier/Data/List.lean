/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Data/List
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Data/List
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
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
lemma ne_nil_of_head?_eq_some {α : Type*} {l : List α} {x : α} (h : l.head? = some x) : l ≠ [] := by
  by_contra heq
  rw [heq] at h
  simp only [head?_nil, reduceCtorEq] at h
namespace Nat
@[simp] lemma eq_of_le_zero {n : ℕ} (h : n ≤ 0) : n = 0 :=
  le_antisymm h (Nat.zero_le _)
end Nat
lemma get_idxOf_of_mem {l : List α} {x : α} (h : x ∈ l) :
  l.get ⟨idxOf x l, idxOf_lt_length_of_mem h⟩ = x := by
  simp [get_eq_getElem]
end List
