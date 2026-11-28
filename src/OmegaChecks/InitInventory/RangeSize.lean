module
public import Lean

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u

namespace RangeSize

open Std Std.PRange

/-- A one-element enumeration in which the only element has no successor. -/
@[instance_reducible] private def terminal : UpwardEnumerable Unit where
  succ? _ := none

/-- A dense comparison on the one-element range has size one. Positivity recovers the comparison. -/
theorem emOfClosed (sizeLaw : type_of% @Rxc.size_pos_iff_le.{0}) (p : Prop) : p ∨ ¬p := by
  letI := terminal
  letI : LE Unit := ⟨fun _ _ => p ∨ ¬p⟩
  letI : Rxc.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Rxc.LawfulHasSize Unit := {
    size_eq_zero_of_not_le := fun _ _ neither => (neither (.inr fun hp => neither (.inl hp))).elim
    size_eq_one_of_succ?_eq_none := fun _ _ _ _ => rfl
    size_eq_succ_of_succ?_eq_some := fun _ _ _ _ eq => nomatch eq
  }
  exact (sizeLaw (lo := ()) (hi := ())).mp (Nat.zero_lt_succ 0)

theorem emOfOpen (sizeLaw : type_of% @Rxo.size_pos_iff_lt.{0}) (p : Prop) : p ∨ ¬p := by
  letI := terminal
  letI : LT Unit := ⟨fun _ _ => p ∨ ¬p⟩
  letI : Rxo.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Rxo.LawfulHasSize Unit := {
    size_eq_zero_of_not_le := fun _ _ neither => (neither (.inr fun hp => neither (.inl hp))).elim
    size_eq_one_of_succ?_eq_none := fun _ _ _ _ => rfl
    size_eq_succ_of_succ?_eq_some := fun _ _ _ _ eq => nomatch eq
  }
  exact (sizeLaw (lo := ()) (hi := ())).mp (Nat.zero_lt_succ 0)

private theorem positive {p : Prop} {n : Nat} (em : ∀ r : Prop, r ∨ ¬r)
    (empty : ¬p → n = 0) (nonempty : p → n ≠ 0) : 0 < n ↔ p :=
  ⟨fun pos => (em p).elim id fun no => (Nat.ne_of_gt pos (empty no)).elim,
   fun yes => Nat.pos_of_ne_zero (nonempty yes)⟩

theorem closedOfEM (em : ∀ p : Prop, p ∨ ¬p) : type_of% @Rxc.size_pos_iff_le.{u} := by
  intro α _ _ _ _ lo hi
  apply positive em (Rxc.size_eq_zero_of_not_le lo hi)
  intro h
  cases s : UpwardEnumerable.succ? lo with
  | none =>
    rw [Rxc.size_eq_one_of_succ?_eq_none lo hi h s]
    exact fun eq => nomatch eq
  | some k =>
    rw [Rxc.size_eq_succ_of_succ?_eq_some lo hi k h s]
    exact fun eq => nomatch eq

theorem openOfEM (em : ∀ p : Prop, p ∨ ¬p) : type_of% @Rxo.size_pos_iff_lt.{u} := by
  intro α _ _ _ _ lo hi
  apply positive em (Rxo.size_eq_zero_of_not_le lo hi)
  intro h
  cases s : UpwardEnumerable.succ? lo with
  | none =>
    rw [Rxo.size_eq_one_of_succ?_eq_none lo hi h s]
    exact fun eq => nomatch eq
  | some k =>
    rw [Rxo.size_eq_succ_of_succ?_eq_some lo hi k h s]
    exact fun eq => nomatch eq

end RangeSize

end OmegaChecks.InitBoundaries
