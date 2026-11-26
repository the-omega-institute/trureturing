module
import all Init.Data.Range.Polymorphic.RangeIterator

/-! A finite successor witness bounds the accessibility proof for each range iterator. -/

open Std Std.PRange Std.PRange.UpwardEnumerable Std.Iterators
namespace OmegaChecks.InitPort.Alternatives

public theorem Std.PRange.UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany? :
    type_of% @_root_.Std.PRange.UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany? := by
  intro α inst law n a
  induction n generalizing a with
  | zero =>
    rw [LawfulUpwardEnumerable.succMany?_add_one, LawfulUpwardEnumerable.succMany?_zero]
    cases ha : succ? a with
    | none => exact ha
    | some b => exact ha.trans (LawfulUpwardEnumerable.succMany?_zero b).symm
  | succ n ih =>
    rw [LawfulUpwardEnumerable.succMany?_add_one, ih (a := a)]
    cases e : succ? a with
    | none => rfl
    | some b => exact (LawfulUpwardEnumerable.succMany?_add_one n b).symm

private theorem accessibleRange {α I : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (iter : Option α → I) (R : I → I → Prop) (allows : α → Prop)
    (finite : ∀ a, ∃ n, (succMany? n a).elim True (fun x => ¬allows x))
    (step : ∀ {next it'}, R it' (iter next) → ∃ a, next = some a ∧ allows a ∧ it' = iter (succ? a))
    (next : Option α) : Acc R (iter next) := by
  have done : Acc R (iter none) := .intro _ fun it' h => by
    obtain ⟨a, noneEq, _, _⟩ := step h
    cases noneEq
  cases next with
  | none => exact done
  | some a =>
    obtain ⟨n, stops⟩ := finite a
    induction n generalizing a with
    | zero =>
      rw [LawfulUpwardEnumerable.succMany?_zero] at stops
      exact .intro _ fun it' h => by
        obtain ⟨b, eq, ok, _⟩ := step h
        cases Option.some.inj eq
        exact (stops ok).elim
    | succ n ih =>
      exact .intro _ fun it' h => by
        obtain ⟨b, eq, _, tail⟩ := step h
        cases Option.some.inj eq
        cases tail
        rw [Std.PRange.UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?] at stops
        cases hNext : succ? a with
        | none => exact done
        | some b => exact ih b (by simpa only [hNext, Option.bind_some] using stops)

public theorem Std.Rxi.Iterator.Monadic.isPlausibleSuccessorOf_iff :
    type_of% @_root_.Std.Rxi.Iterator.Monadic.isPlausibleSuccessorOf_iff := by
  intro α inst q p
  rcases p with ⟨⟨o⟩⟩
  rcases q with ⟨⟨o'⟩⟩
  cases o with
  | none =>
    constructor
    · intro ⟨step, e, agrees⟩
      cases agrees
      cases e
    · intro ⟨a, e, _⟩
      cases e
  | some a =>
    constructor
    · intro ⟨step, e, agrees⟩
      cases agrees
      have eq := Option.some.inj e
      exact ⟨a, rfl, congrArg (fun it : IterM (α := Rxi.Iterator α) Id α => it.internalState.next) eq⟩
    · intro ⟨b, eq, target⟩
      cases Option.some.inj eq
      cases target
      exact ⟨.yield _ a, rfl, rfl⟩

public theorem Std.Rxc.Iterator.instFinitenessRelation._proof_1 :
    type_of% (private_decl% @_root_.Std.Rxc.Iterator.instFinitenessRelation._proof_1) := by
  intro α en ord dec law finite
  constructor
  rintro ⟨⟨next, upper⟩⟩
  apply accessibleRange (fun o => (⟨⟨o, upper⟩⟩ : IterM (α := Rxc.Iterator α) Id α))
    (fun a b => a.IsPlausibleSuccessorOf b) (· ≤ upper) (fun a => Rxc.IsAlwaysFinite.finite a upper) _ next
  rintro o ⟨⟨next', bound'⟩⟩ h
  obtain ⟨a, eq, allowed, nextEq, boundEq⟩ := _root_.Std.Rxc.Iterator.Monadic.isPlausibleSuccessorOf_iff.mp h
  exact ⟨a, eq, allowed, by cases boundEq; cases nextEq; rfl⟩

public theorem Std.Rxo.Iterator.instFinitenessRelation._proof_1 :
    type_of% (private_decl% @_root_.Std.Rxo.Iterator.instFinitenessRelation._proof_1) := by
  intro α en ord dec law finite
  constructor
  rintro ⟨⟨next, upper⟩⟩
  apply accessibleRange (fun o => (⟨⟨o, upper⟩⟩ : IterM (α := Rxo.Iterator α) Id α))
    (fun a b => a.IsPlausibleSuccessorOf b) (· < upper) (fun a => Rxo.IsAlwaysFinite.finite a upper) _ next
  rintro o ⟨⟨next', bound'⟩⟩ h
  obtain ⟨a, eq, allowed, nextEq, boundEq⟩ := _root_.Std.Rxo.Iterator.Monadic.isPlausibleSuccessorOf_iff.mp h
  exact ⟨a, eq, allowed, by cases boundEq; cases nextEq; rfl⟩

public theorem Std.Rxi.Iterator.instFinitenessRelation._proof_1 :
    type_of% (private_decl% @_root_.Std.Rxi.Iterator.instFinitenessRelation._proof_1) := by
  intro α en law finite
  constructor
  rintro ⟨⟨next⟩⟩
  apply accessibleRange (fun o => (⟨⟨o⟩⟩ : IterM (α := Rxi.Iterator α) Id α))
    (fun a b => a.IsPlausibleSuccessorOf b) (fun _ => True) _ _ next
  · intro a
    obtain ⟨n, h⟩ := Rxi.IsAlwaysFinite.finite a
    exact ⟨n, by rw [h]; exact True.intro⟩
  · rintro o ⟨⟨next'⟩⟩ h
    obtain ⟨a, eq, nextEq⟩ := Std.Rxi.Iterator.Monadic.isPlausibleSuccessorOf_iff.mp h
    exact ⟨a, eq, True.intro, by cases nextEq; rfl⟩

end OmegaChecks.InitPort.Alternatives
