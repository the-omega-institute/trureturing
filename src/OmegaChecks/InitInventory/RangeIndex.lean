module
public import Init.Data.Range.Polymorphic.NatLemmas
public import Lean

/-! Exact arithmetic conditions for Boolean lookup flags over each natural-number range. -/

public section
namespace OmegaChecks.InitBoundaries.RangeIndex

abbrev NormalLE (a b : Nat) : Prop := (decide (a ≤ b) = true) = (a ≤ b)
abbrev NormalLT (a b : Nat) : Prop := (decide (a < b) = true) = (a < b)

/-- The Boolean decision for any weak comparison reflects the comparison as an equality of propositions. -/
def LEReflection := ∀ a b : Nat, NormalLE a b

/-- The corresponding reflection principle for strict comparisons. -/
def LTReflection := ∀ a b : Nat, NormalLT a b

/-- For an open interval, an unsuccessful lookup compares the upper endpoint to a positive bound. -/
def LEPositiveRight := ∀ a b : Nat, NormalLE a (b + 1)

private theorem normalized {p : Prop} [Decidable p] {b : Bool} (correct : b = true ↔ p) :
    ((b = true) = p) ↔ ((decide p = true) = p) := by
  have eq : b = decide p := by
    cases h : b with
    | false => exact (decide_eq_false (fun hp => Bool.noConfusion (h.symm.trans (correct.mpr hp)))).symm
    | true => exact (decide_eq_true (correct.mp h)).symm
  cases eq
  exact Iff.rfl

private theorem hit {α : Type} {answer : Option α} {x : α} {p : Prop} [Decidable p]
    (lookup : answer = if p then some x else none) :
    ((answer.isSome = true) = p) ↔ ((decide p = true) = p) := by
  apply normalized
  cases lookup
  by_cases h : p
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]
    exact ⟨(fun eq => nomatch eq), fun hp => (h hp).elim⟩

private theorem miss {α : Type} {answer : Option α} {p : Prop} [Decidable p]
    (none_iff : answer = none ↔ p) :
    ((answer.isNone = true) = p) ↔ ((decide p = true) = p) :=
  normalized (Option.isNone_iff_eq_none.trans none_iff)

theorem someListRco : (type_of% @Nat.isSome_getElem?_toList_rco_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toList_rco (m := 0) (n := b) (i := a))).mp (@rule 0 b a)
  · intro r m n i
    exact (hit Nat.getElem?_toList_rco).mpr (r i (n - m))

theorem someListRoc : (type_of% @Nat.isSome_getElem?_toList_roc_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toList_roc (m := 0) (n := b) (i := a))).mp (@rule 0 b a)
  · intro r m n i
    exact (hit Nat.getElem?_toList_roc).mpr (r i (n - m))

theorem someListRoo : (type_of% @Nat.isSome_getElem?_toList_roo_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toList_roo (m := 0) (n := b + 1) (i := a))).mp (@rule 0 (b + 1) a)
  · intro r m n i
    exact (hit Nat.getElem?_toList_roo).mpr (r i (n - (m + 1)))

theorem someListRcc : (type_of% @Nat.isSome_getElem?_toList_rcc_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toList_rcc (m := 1) (n := b) (i := a))).mp (@rule 1 b a)
  · intro r m n i
    exact (hit Nat.getElem?_toList_rcc).mpr (r i (n + 1 - m))

theorem someListRio : (type_of% @Nat.isSome_getElem?_toList_rio_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toList_rio (n := b) (i := a))).mp (@rule b a)
  · intro r n i
    exact (hit Nat.getElem?_toList_rio).mpr (r i n)

theorem someListRic : (type_of% @Nat.isSome_getElem?_toList_ric_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toList_ric (n := b) (i := a))).mp (@rule b a)
  · intro r n i
    exact (hit Nat.getElem?_toList_ric).mpr (r i n)

theorem noneListRco : (type_of% @Nat.isNone_getElem?_toList_rco_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toList_rco_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toList_rco_eq_none_iff).mpr (r n (i + m))

theorem noneListRoc : (type_of% @Nat.isNone_getElem?_toList_roc_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toList_roc_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toList_roc_eq_none_iff).mpr (r n (i + m))

theorem noneListRoo : (type_of% @Nat.isNone_getElem?_toList_roo_eq) ↔ LEPositiveRight := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toList_roo_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toList_roo_eq_none_iff).mpr (r n (i + m))

theorem noneListRcc : (type_of% @Nat.isNone_getElem?_toList_rcc_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toList_rcc_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toList_rcc_eq_none_iff).mpr (r n (i + m))

theorem noneListRio : (type_of% @Nat.isNone_getElem?_toList_rio_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toList_rio_eq_none_iff (n := a) (i := b))).mp (@rule a b)
  · intro r n i
    exact (miss Nat.getElem?_toList_rio_eq_none_iff).mpr (r n i)

theorem noneListRic : (type_of% @Nat.isNone_getElem?_toList_ric_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toList_ric_eq_none_iff (n := a) (i := b))).mp (@rule a b)
  · intro r n i
    exact (miss Nat.getElem?_toList_ric_eq_none_iff).mpr (r n i)

theorem someArrayRco : (type_of% @Nat.isSome_getElem?_toArray_rco_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toArray_rco (m := 0) (n := b) (i := a))).mp (@rule 0 b a)
  · intro r m n i
    exact (hit Nat.getElem?_toArray_rco).mpr (r i (n - m))

theorem someArrayRoc : (type_of% @Nat.isSome_getElem?_toArray_roc_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toArray_roc (m := 0) (n := b) (i := a))).mp (@rule 0 b a)
  · intro r m n i
    exact (hit Nat.getElem?_toArray_roc).mpr (r i (n - m))

theorem someArrayRoo : (type_of% @Nat.isSome_getElem?_toArray_roo_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toArray_roo (m := 0) (n := b + 1) (i := a))).mp (@rule 0 (b + 1) a)
  · intro r m n i
    exact (hit Nat.getElem?_toArray_roo).mpr (r i (n - (m + 1)))

theorem someArrayRcc : (type_of% @Nat.isSome_getElem?_toArray_rcc_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toArray_rcc (m := 1) (n := b) (i := a))).mp (@rule 1 b a)
  · intro r m n i
    exact (hit Nat.getElem?_toArray_rcc).mpr (r i (n + 1 - m))

theorem someArrayRio : (type_of% @Nat.isSome_getElem?_toArray_rio_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toArray_rio (n := b) (i := a))).mp (@rule b a)
  · intro r n i
    exact (hit Nat.getElem?_toArray_rio).mpr (r i n)

theorem someArrayRic : (type_of% @Nat.isSome_getElem?_toArray_ric_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (hit (Nat.getElem?_toArray_ric (n := b) (i := a))).mp (@rule b a)
  · intro r n i
    exact (hit Nat.getElem?_toArray_ric).mpr (r i n)

theorem noneArrayRco : (type_of% @Nat.isNone_getElem?_toArray_rco_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toArray_rco_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toArray_rco_eq_none_iff).mpr (r n (i + m))

theorem noneArrayRoc : (type_of% @Nat.isNone_getElem?_toArray_roc_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toArray_roc_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toArray_roc_eq_none_iff).mpr (r n (i + m))

theorem noneArrayRoo : (type_of% @Nat.isNone_getElem?_toArray_roo_eq) ↔ LEPositiveRight := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toArray_roo_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toArray_roo_eq_none_iff).mpr (r n (i + m))

theorem noneArrayRcc : (type_of% @Nat.isNone_getElem?_toArray_rcc_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toArray_rcc_eq_none_iff (m := 0) (n := a) (i := b))).mp (@rule 0 a b)
  · intro r m n i
    exact (miss Nat.getElem?_toArray_rcc_eq_none_iff).mpr (r n (i + m))

theorem noneArrayRio : (type_of% @Nat.isNone_getElem?_toArray_rio_eq) ↔ LEReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toArray_rio_eq_none_iff (n := a) (i := b))).mp (@rule a b)
  · intro r n i
    exact (miss Nat.getElem?_toArray_rio_eq_none_iff).mpr (r n i)

theorem noneArrayRic : (type_of% @Nat.isNone_getElem?_toArray_ric_eq) ↔ LTReflection := by
  constructor
  · intro rule a b
    exact (miss (Nat.getElem?_toArray_ric_eq_none_iff (n := a) (i := b))).mp (@rule a b)
  · intro r n i
    exact (miss Nat.getElem?_toArray_ric_eq_none_iff).mpr (r n i)

open Lean in
def equivalences : List (Name × Name × Name) := [
  (``Nat.isSome_getElem?_toList_rco_eq, ``LTReflection, ``someListRco),
  (``Nat.isSome_getElem?_toList_roc_eq, ``LTReflection, ``someListRoc),
  (``Nat.isSome_getElem?_toList_roo_eq, ``LTReflection, ``someListRoo),
  (``Nat.isSome_getElem?_toList_rcc_eq, ``LTReflection, ``someListRcc),
  (``Nat.isSome_getElem?_toList_rio_eq, ``LTReflection, ``someListRio),
  (``Nat.isSome_getElem?_toList_ric_eq, ``LEReflection, ``someListRic),
  (``Nat.isNone_getElem?_toList_rco_eq, ``LEReflection, ``noneListRco),
  (``Nat.isNone_getElem?_toList_roc_eq, ``LEReflection, ``noneListRoc),
  (``Nat.isNone_getElem?_toList_roo_eq, ``LEPositiveRight, ``noneListRoo),
  (``Nat.isNone_getElem?_toList_rcc_eq, ``LTReflection, ``noneListRcc),
  (``Nat.isNone_getElem?_toList_rio_eq, ``LEReflection, ``noneListRio),
  (``Nat.isNone_getElem?_toList_ric_eq, ``LTReflection, ``noneListRic),
  (``Nat.isSome_getElem?_toArray_rco_eq, ``LTReflection, ``someArrayRco),
  (``Nat.isSome_getElem?_toArray_roc_eq, ``LTReflection, ``someArrayRoc),
  (``Nat.isSome_getElem?_toArray_roo_eq, ``LTReflection, ``someArrayRoo),
  (``Nat.isSome_getElem?_toArray_rcc_eq, ``LTReflection, ``someArrayRcc),
  (``Nat.isSome_getElem?_toArray_rio_eq, ``LTReflection, ``someArrayRio),
  (``Nat.isSome_getElem?_toArray_ric_eq, ``LEReflection, ``someArrayRic),
  (``Nat.isNone_getElem?_toArray_rco_eq, ``LEReflection, ``noneArrayRco),
  (``Nat.isNone_getElem?_toArray_roc_eq, ``LEReflection, ``noneArrayRoc),
  (``Nat.isNone_getElem?_toArray_roo_eq, ``LEPositiveRight, ``noneArrayRoo),
  (``Nat.isNone_getElem?_toArray_rcc_eq, ``LTReflection, ``noneArrayRcc),
  (``Nat.isNone_getElem?_toArray_rio_eq, ``LEReflection, ``noneArrayRio),
  (``Nat.isNone_getElem?_toArray_ric_eq, ``LTReflection, ``noneArrayRic)]

end OmegaChecks.InitBoundaries.RangeIndex
