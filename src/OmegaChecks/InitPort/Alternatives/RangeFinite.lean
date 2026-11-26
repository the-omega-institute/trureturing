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

public theorem Std.Rxc.Iterator.step_eq_monadicStep : type_of% @_root_.Std.Rxc.Iterator.step_eq_monadicStep := by
  intro α en ord dec it
  rcases it with ⟨⟨_ | a, upper⟩⟩
  · rfl
  · by_cases bound : a ≤ upper <;>
      simp only [Rxc.Iterator.step, Rxc.Iterator.Monadic.step, Iter.toIterM, bound,
        ite_true, ite_false, IterStep.mapIterator, IterM.toIter]

public theorem Std.Rxo.Iterator.step_eq_monadicStep : type_of% @_root_.Std.Rxo.Iterator.step_eq_monadicStep := by
  intro α en ord dec it
  rcases it with ⟨⟨_ | a, upper⟩⟩
  · rfl
  · by_cases bound : a < upper <;>
      simp only [Rxo.Iterator.step, Rxo.Iterator.Monadic.step, Iter.toIterM, bound,
        ite_true, ite_false, IterStep.mapIterator, IterM.toIter]

public theorem Std.Rxi.Iterator.Monadic.isPlausibleOutput_iff :
    type_of% @_root_.Std.Rxi.Iterator.Monadic.isPlausibleOutput_iff := by
  intro α a en it
  rcases it with ⟨⟨_ | b⟩⟩
  · constructor
    · rintro ⟨_, eq⟩
      cases eq
    · intro eq
      cases eq
  · constructor
    · rintro ⟨_, eq⟩
      cases eq
      rfl
    · intro eq
      cases Option.some.inj eq
      exact ⟨_, rfl⟩

public theorem Std.Rxi.Iterator.isPlausibleOutput_iff :
    type_of% @_root_.Std.Rxi.Iterator.isPlausibleOutput_iff := by
  intro α a en it
  exact Std.Rxi.Iterator.Monadic.isPlausibleOutput_iff

public theorem Std.Rxi.Iterator.isPlausibleOutput_next :
    type_of% @_root_.Std.Rxi.Iterator.isPlausibleOutput_next := by
  intro α a en it h
  exact Std.Rxi.Iterator.isPlausibleOutput_iff.mpr h

private theorem rangeIndirectOutput {σ α : Type u} [Iterator σ Id α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    (next : IterM (α := σ) Id α → Option α)
    (allows : IterM (α := σ) Id α → α → Prop)
    (output : ∀ {it a}, it.IsPlausibleOutput a ↔ next it = some a ∧ allows it a)
    (forward : ∀ {it it'}, it'.IsPlausibleSuccessorOf it →
      ∃ a, next it = some a ∧ succ? a = next it' ∧ ∀ b, allows it' b → allows it b)
    (back : ∀ {it a n b}, next it = some a → succMany? (n + 1) a = some b → allows it b →
      ∃ it', it'.IsPlausibleSuccessorOf it ∧ succ? a = next it' ∧ allows it' b)
    {it : IterM (α := σ) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔ ∃ n, (next it).bind (succMany? n) = some out ∧ allows it out := by
  constructor
  · intro h
    induction h with
    | direct h =>
      obtain ⟨start, ok⟩ := output.mp h
      exact ⟨0, by rw [start]; exact LawfulUpwardEnumerable.succMany?_zero _, ok⟩
    | indirect h _ ih =>
      obtain ⟨a, start, tail, ok⟩ := forward h
      obtain ⟨n, reaches, allowed⟩ := ih
      refine ⟨n + 1, ?_, ok _ allowed⟩
      rw [start, Option.bind_some, Std.PRange.UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, tail]
      exact reaches
  · rintro ⟨n, reaches, allowed⟩
    induction n generalizing it with
    | zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      apply output.mpr
      refine ⟨?_, allowed⟩
      cases start : next it with
      | none => rw [start] at reaches; cases reaches
      | some a =>
        rw [start, Option.bind_some, LawfulUpwardEnumerable.succMany?_zero] at reaches
        exact reaches
    | succ n ih =>
      cases start : next it with
      | none => rw [start] at reaches; cases reaches
      | some a =>
        rw [start, Option.bind_some] at reaches
        obtain ⟨it', step, tail, allowed'⟩ := back start reaches allowed
        apply IterM.IsPlausibleIndirectOutput.indirect step
        apply ih (it := it') _ allowed'
        rw [← tail, ← Std.PRange.UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
        exact reaches

public theorem Std.Rxc.Iterator.Monadic.isPlausibleIndirectOutput_iff :
    type_of% @_root_.Std.Rxc.Iterator.Monadic.isPlausibleIndirectOutput_iff := by
  intro α en ord dec laws lawful it out
  apply rangeIndirectOutput (fun it : IterM (α := Rxc.Iterator α) Id α => it.internalState.next)
    (fun it a => a ≤ it.internalState.upperBound) _root_.Std.Rxc.Iterator.Monadic.isPlausibleOutput_iff
  · intro it it' h
    obtain ⟨a, start, _, tail, bound⟩ := _root_.Std.Rxc.Iterator.Monadic.isPlausibleSuccessorOf_iff.mp h
    exact ⟨a, start, tail, fun _ ok => bound ▸ ok⟩
  · intro it a n b start reaches allowed
    refine ⟨⟨⟨succ? a, it.internalState.upperBound⟩⟩,
      _root_.Std.Rxc.Iterator.Monadic.isPlausibleSuccessorOf_iff.mpr ⟨a, start, ?_, rfl, rfl⟩, rfl, allowed⟩
    letI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
    exact Trans.trans (α := α) (r := (· ≤ ·)) (UpwardEnumerable.le_iff.mpr ⟨_, reaches⟩) allowed

public theorem Std.Rxo.Iterator.Monadic.isPlausibleIndirectOutput_iff :
    type_of% @_root_.Std.Rxo.Iterator.Monadic.isPlausibleIndirectOutput_iff := by
  intro α en ord dec laws lawful it out
  apply rangeIndirectOutput (fun it : IterM (α := Rxo.Iterator α) Id α => it.internalState.next)
    (fun it a => a < it.internalState.upperBound) _root_.Std.Rxo.Iterator.Monadic.isPlausibleOutput_iff
  · intro it it' h
    obtain ⟨a, start, _, tail, bound⟩ := _root_.Std.Rxo.Iterator.Monadic.isPlausibleSuccessorOf_iff.mp h
    exact ⟨a, start, tail, fun _ ok => bound ▸ ok⟩
  · intro it a n b start reaches allowed
    refine ⟨⟨⟨succ? a, it.internalState.upperBound⟩⟩,
      _root_.Std.Rxo.Iterator.Monadic.isPlausibleSuccessorOf_iff.mpr ⟨a, start, ?_, rfl, rfl⟩, rfl, allowed⟩
    letI := UpwardEnumerable.instLTTransOfLawfulUpwardEnumerableLT (α := α)
    exact Trans.trans (α := α) (r := (· < ·)) (UpwardEnumerable.lt_iff.mpr ⟨_, reaches⟩) allowed

public theorem Std.Rxi.Iterator.Monadic.isPlausibleIndirectOutput_iff :
    type_of% @_root_.Std.Rxi.Iterator.Monadic.isPlausibleIndirectOutput_iff := by
  intro α en lawful it out
  have reach := rangeIndirectOutput (fun it : IterM (α := Rxi.Iterator α) Id α => it.internalState.next)
    (fun _ _ => True) (fun {it a} => ?_) (fun {it it'} h => ?_) (fun {it a n b} start _ _ => ?_)
    (it := it) (out := out)
  · exact reach.trans ⟨fun ⟨n, h, _⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, h, True.intro⟩⟩
  · exact Std.Rxi.Iterator.Monadic.isPlausibleOutput_iff.trans ⟨fun h => ⟨h, True.intro⟩, And.left⟩
  · obtain ⟨a, start, tail⟩ := Std.Rxi.Iterator.Monadic.isPlausibleSuccessorOf_iff.mp h
    exact ⟨a, start, tail, fun _ _ => True.intro⟩
  · exact ⟨⟨⟨succ? a⟩⟩, Std.Rxi.Iterator.Monadic.isPlausibleSuccessorOf_iff.mpr ⟨a, start, rfl⟩,
      rfl, True.intro⟩

public theorem Std.Rxc.Iterator.isPlausibleIndirectOutput_iff :
    type_of% @_root_.Std.Rxc.Iterator.isPlausibleIndirectOutput_iff := by
  intro α en ord dec lawful laws it out
  exact Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.trans
    Std.Rxc.Iterator.Monadic.isPlausibleIndirectOutput_iff

public theorem Std.Rxo.Iterator.isPlausibleIndirectOutput_iff :
    type_of% @_root_.Std.Rxo.Iterator.isPlausibleIndirectOutput_iff := by
  intro α en ord dec lawful laws it out
  exact Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.trans
    Std.Rxo.Iterator.Monadic.isPlausibleIndirectOutput_iff

public theorem Std.Rxi.Iterator.isPlausibleIndirectOutput_iff :
    type_of% @_root_.Std.Rxi.Iterator.isPlausibleIndirectOutput_iff := by
  intro α en lawful it out
  exact Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.trans
    Std.Rxi.Iterator.Monadic.isPlausibleIndirectOutput_iff

end OmegaChecks.InitPort.Alternatives
