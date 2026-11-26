module

public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Iterators.Combinators.Monadic.Take
public import Init.Data.Range.Polymorphic.Instances

/-! Finite consumers have a well-founded relation in their own interface. -/

open Std Std.PRange Std.Iterators Std.Iterators.Types

namespace OmegaChecks.InitPort.Alternatives

private theorem collectorWF {α β σ : Type u} {m : Type u → Type v}
    [Iterator α m β] [Finite α m] :
    WellFounded (InvImage IterM.TerminationMeasures.Finite.Rel
      (fun p : (_ : IterM (α := α) m β) ×' σ => p.1.finitelyManySteps!)) :=
  InvImage.wf _ (IterM.TerminationMeasures.instWellFoundedRelationFinite (α := α) (m := m)).wf

public noncomputable def Std.IterM.Total.toArray
    {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m] [Iterator α m β]
    [Finite α m] (it : IterM.Total (α := α) m β) : m (Array β) :=
  (collectorWF (α := α) (β := β) (m := m) (σ := Array β)).fix (C := fun _ => m (Array β))
    (fun p recur => do
      match (← p.1.step).inflate with
      | .yield next out h => recur ⟨next, p.2.push out⟩ (IterM.TerminationMeasures.Finite.rel_of_yield h)
      | .skip next h => recur ⟨next, p.2⟩ (IterM.TerminationMeasures.Finite.rel_of_skip h)
      | .done _ => return p.2) ⟨it.it, #[]⟩

public noncomputable def Std.IterM.Total.toListRev
    {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m] [Iterator α m β]
    [Finite α m] (it : IterM.Total (α := α) m β) : m (List β) :=
  (collectorWF (α := α) (β := β) (m := m) (σ := List β)).fix (C := fun _ => m (List β))
    (fun p recur => do
      match (← p.1.step).inflate with
      | .yield next out h => recur ⟨next, out :: p.2⟩ (IterM.TerminationMeasures.Finite.rel_of_yield h)
      | .skip next h => recur ⟨next, p.2⟩ (IterM.TerminationMeasures.Finite.rel_of_skip h)
      | .done _ => return p.2) ⟨it.it, []⟩

public def Std.IterM.Total.toList {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) : m (List β) :=
  Array.toList <$> _root_.Std.IterM.Total.toArray it

/-- A decreasing countdown suffices. At equal countdowns, a finite inner iterator
also allows yielding steps to contribute to the decrease. -/
public def Std.Iterators.Types.Take.Rel {α β : Type w} (m : Type w → Type v)
    [Monad m] [Iterator α m β] [Productive α m] (a b : IterM (α := Take α m) m β) : Prop :=
  a.internalState.countdown < b.internalState.countdown ∨
    a.internalState.countdown = b.internalState.countdown ∧
      (a.internalState.inner.finitelyManySkips.Rel b.internalState.inner.finitelyManySkips ∨
        Finite α m ∧ a.internalState.inner.finitelyManySteps!.Rel b.internalState.inner.finitelyManySteps!)

public theorem Std.Iterators.Types.Take.rel_of_countdown {α : Type w} {m : Type w → Type v}
    {β : Type w} [Monad m] [Iterator α m β] [Productive α m] {it it' : IterM (α := Take α m) m β}
    (h : it'.internalState.countdown < it.internalState.countdown) :
    Std.Iterators.Types.Take.Rel m it' it := Or.inl h

public theorem Std.Iterators.Types.Take.rel_of_inner {α : Type w} {m : Type w → Type v}
    {β : Type w} [Monad m] [Iterator α m β] [Productive α m] {remaining : Nat}
    {it it' : IterM (α := α) m β} (h : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Std.Iterators.Types.Take.Rel m (it'.take remaining) (it.take remaining) := Or.inr ⟨rfl, Or.inl h⟩

public theorem Std.Iterators.Types.Take.rel_of_zero_of_inner {α : Type w} {m : Type w → Type v}
    {β : Type w} [Monad m] [Iterator α m β] {it it' : IterM (α := Take α m) m β}
    (h : it.internalState.countdown = 0) (h' : it'.internalState.countdown = 0)
    (h'' : it'.internalState.inner.finitelyManySteps!.Rel it.internalState.inner.finitelyManySteps!) :
    letI : Finite α m := it.internalState.finite.resolve_left (fun hp => Nat.not_lt_zero _ (h ▸ hp))
    Std.Iterators.Types.Take.Rel m it' it := by
  have hf := it.internalState.finite.resolve_left (fun hp => Nat.not_lt_zero _ (h ▸ hp))
  exact Or.inr ⟨h'.trans h.symm, Or.inr ⟨hf, h''⟩⟩

public theorem Std.Iterators.Types.Take.instFinite {α : Type u} {m : Type u → Type v} {β : Type u}
    [Monad m] [Iterator α m β] [Productive α m] : Finite (Take α m) m := by
  let T := IterM (α := Take α m) m β
  let R := IterM.IsPlausibleSuccessorOf (α := Take α m) (m := m)
  have finiteInner (hf : Finite α m) (inner : IterM (α := α) m β) :
      ∀ (n : Nat) (h : 0 < n ∨ Finite α m), Acc R (⟨n, inner, h⟩ : T) := by
    induction inner using hf.wf.induction with
    | h it ih =>
      intro n h
      constructor
      rintro _ ⟨_, heq, hs⟩
      cases hs with
      | yield hy _ => cases heq; exact ih _ (IterM.isPlausibleSuccessorOf_of_yield hy) _ _
      | skip hs _ => cases heq; exact ih _ (IterM.isPlausibleSuccessorOf_of_skip hs) _ _
      | done _ => cases heq
      | depleted _ => cases heq
  have positive (n : Nat) : ∀ (hp : 0 < n) (inner : IterM (α := α) m β),
      Acc R (⟨n, inner, Or.inl hp⟩ : T) := by
    induction n using Nat.strongRecOn with
    | ind n smaller =>
      intro hp inner
      induction inner using (Productive.wf (α := α) (m := m) (β := β)).induction with
      | h it fewerSkips =>
        constructor
        rintro _ ⟨_, heq, hs⟩
        cases hs with
        | yield _ hne =>
          cases heq
          change n ≠ 1 at hne
          apply smaller (n - 1) (Nat.sub_lt hp (by decide))
          exact Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne hp (Ne.symm hne))
        | skip hs _ => cases heq; exact fewerSkips _ hs
        | done _ => cases heq
        | depleted _ => cases heq
  refine ⟨⟨?_⟩⟩
  rintro ⟨n, inner, h⟩
  cases h with
  | inl hp => exact positive n hp inner
  | inr hf => exact finiteInner hf inner n (Or.inr hf)

public theorem Std.IteratorLoop.wellFounded_of_productive.{w, v, x} :
    type_of% @_root_.Std.IteratorLoop.wellFounded_of_productive.{w, v, x} := by
  intro γ α β m _ _ _ P hp
  apply Subrelation.wf (r := InvImage (IterM.IsPlausibleSkipSuccessorOf (α := α) (m := m)) Prod.fst)
  · intro p' p h
    rcases h with ⟨_, _, hy⟩ | ⟨hs, _⟩
    · exact Bool.noConfusion (hp hy)
    · exact hs
  · exact InvImage.wf _ Productive.wf

public theorem Std.Rxc.size_eq_zero_iff_not_le : type_of% @_root_.Std.Rxc.size_eq_zero_iff_not_le := by
  intro α _ _ _ _ lo hi
  refine ⟨fun hzero hle => ?_, Rxc.LawfulHasSize.size_eq_zero_of_not_le lo hi⟩
  cases hs : UpwardEnumerable.succ? lo with
  | none => exact Nat.noConfusion (hzero.symm.trans
      (Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (h := hle) (h' := hs)))
  | some next => exact Nat.noConfusion (hzero.symm.trans
      (Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hle) (h' := hs)))

public theorem Std.Rxo.size_eq_zero_iff_not_le : type_of% @_root_.Std.Rxo.size_eq_zero_iff_not_le := by
  intro α _ _ _ _ lo hi
  refine ⟨fun hzero hlt => ?_, Rxo.LawfulHasSize.size_eq_zero_of_not_le lo hi⟩
  cases hs : UpwardEnumerable.succ? lo with
  | none => exact Nat.noConfusion (hzero.symm.trans
      (Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none (h := hlt) (h' := hs)))
  | some next => exact Nat.noConfusion (hzero.symm.trans
      (Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hlt) (h' := hs)))

private theorem finiteRangeOfSize [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (within : α → Prop) (size : α → Nat)
    (zero : ∀ lo, size lo = 0 ↔ ¬ within lo)
    (step : ∀ lo next, within lo → UpwardEnumerable.succ? lo = some next → size lo = size next + 1)
    (lo : α) : (UpwardEnumerable.succMany? (size lo) lo).elim True (fun a => ¬ within a) := by
  generalize hn : size lo = n
  induction n generalizing lo with
  | zero =>
    rw [UpwardEnumerable.succMany?_zero]
    exact (zero lo).mp hn
  | succ n ih =>
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact True.intro
    | some next =>
      apply ih
      apply Decidable.byContradiction
      intro hne
      have outside : ¬ within lo := fun h => hne (Nat.succ.inj ((step lo next h hs).symm.trans hn))
      exact Nat.noConfusion (((zero lo).mpr outside).symm.trans hn)

public theorem Std.Rxc.instIsAlwaysFiniteOfLawfulHasSize :
    type_of% @_root_.Std.Rxc.instIsAlwaysFiniteOfLawfulHasSize := by
  intro α _ _ _ _ _
  refine ⟨fun lo hi => ⟨Rxc.HasSize.size lo hi, ?_⟩⟩
  exact finiteRangeOfSize (· ≤ hi) (fun a => Rxc.HasSize.size a hi)
    (fun _ => _root_.Std.Rxc.size_eq_zero_iff_not_le)
    (fun a b => Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some a hi b) lo

public theorem Std.Rxo.instIsAlwaysFiniteOfLawfulHasSize :
    type_of% @_root_.Std.Rxo.instIsAlwaysFiniteOfLawfulHasSize := by
  intro α _ _ _ _ _
  refine ⟨fun lo hi => ⟨Rxo.HasSize.size lo hi, ?_⟩⟩
  exact finiteRangeOfSize (· < hi) (fun a => Rxo.HasSize.size a hi)
    (fun _ => _root_.Std.Rxo.size_eq_zero_iff_not_le)
    (fun a b => Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some a hi b) lo

public theorem Std.Rxi.instIsAlwaysFiniteOfLawfulHasSize :
    type_of% @_root_.Std.Rxi.instIsAlwaysFiniteOfLawfulHasSize := by
  intro α _ _ _ _ _
  constructor
  intro lo
  refine ⟨Rxi.HasSize.size lo, ?_⟩
  generalize hn : Rxi.HasSize.size lo = n
  induction n generalizing lo with
  | zero =>
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact Nat.noConfusion (hn.symm.trans (Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none lo hs))
    | some next => exact Nat.noConfusion (hn.symm.trans (Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some lo next hs))
  | succ n ih =>
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
    cases hs : UpwardEnumerable.succ? lo with
    | none => rfl
    | some next => exact ih next (Nat.succ.inj ((Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some lo next hs).symm.trans hn))

public theorem Std.Rxo.LawfulHasSize.of_closed :
    type_of% @_root_.Std.Rxo.LawfulHasSize.of_closed := by
  intro α _ _ _ _ _ _ _ _ _ _ _
  letI : _root_.Std.Rxo.HasSize α := _root_.Std.Rxo.HasSize.ofClosed
  constructor
  · intro lo hi hnlt
    change Rxc.HasSize.size lo hi - 1 = 0
    by_cases hle : lo ≤ hi
    · cases hs : UpwardEnumerable.succ? lo with
      | none => rw [Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (h := hle) (h' := hs)]
      | some b =>
        have hlt : lo < b := UpwardEnumerable.lt_iff.mpr ⟨0,
          (UpwardEnumerable.succMany?_one (a := lo)).trans hs⟩
        have hnle : ¬ b ≤ hi := fun hb => hnlt (lt_of_lt_of_le hlt hb)
        rw [Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hle) (h' := hs),
          Rxc.LawfulHasSize.size_eq_zero_of_not_le (h := hnle)]
    · rw [Rxc.LawfulHasSize.size_eq_zero_of_not_le (h := hle)]
  · intro lo hi hlt hs
    obtain ⟨n, hn⟩ := UpwardEnumerable.lt_iff.mp hlt
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hn
    cases hn
  · intro lo hi next hlt hs
    change Rxc.HasSize.size lo hi - 1 = Rxc.HasSize.size next hi - 1 + 1
    have hle := le_of_lt hlt
    obtain ⟨n, hn⟩ := UpwardEnumerable.lt_iff.mp hlt
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hn
    have hnext : next ≤ hi := UpwardEnumerable.le_iff.mpr ⟨n, hn⟩
    have hpos := Nat.pos_of_ne_zero fun h => (_root_.Std.Rxc.size_eq_zero_iff_not_le.mp h) hnext
    rw [Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hle) (h' := hs)]
    exact (Nat.sub_add_cancel hpos).symm

variable {α β : Type u} [Iterator α Id β] [Finite α Id]

public def Std.Iter.Total.toArray (it : Iter.Total (α := α) β) : Array β :=
  it.it.toIterM.ensureTermination.toArray.run

public def Std.Iter.Total.toListRev (it : Iter.Total (α := α) β) : List β :=
  it.it.toIterM.ensureTermination.toListRev.run

public def Std.Iter.Total.toList (it : Iter.Total (α := α) β) : List β :=
  it.it.toIterM.ensureTermination.toList.run

public def Std.Rcc.toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Rcc α) : List α :=
  (_root_.Std.Rcc.Internal.iter r).ensureTermination.toList

public def Std.Rcc.toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Rcc α) : Array α :=
  (_root_.Std.Rcc.Internal.iter r).ensureTermination.toArray

public def Std.Rco.toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rco α) : List α :=
  (_root_.Std.Rco.Internal.iter r).ensureTermination.toList

public def Std.Rco.toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rco α) : Array α :=
  (_root_.Std.Rco.Internal.iter r).ensureTermination.toArray

public def Std.Rci.toList [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Rci α) : List α :=
  (_root_.Std.Rci.Internal.iter r).ensureTermination.toList

public def Std.Rci.toArray [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Rci α) : Array α :=
  (_root_.Std.Rci.Internal.iter r).ensureTermination.toArray

public def Std.Roc.toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Roc α) : List α :=
  (_root_.Std.Roc.Internal.iter r).ensureTermination.toList

public def Std.Roc.toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Roc α) : Array α :=
  (_root_.Std.Roc.Internal.iter r).ensureTermination.toArray

public def Std.Roo.toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Roo α) : List α :=
  (_root_.Std.Roo.Internal.iter r).ensureTermination.toList

public def Std.Roo.toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Roo α) : Array α :=
  (_root_.Std.Roo.Internal.iter r).ensureTermination.toArray

public def Std.Roi.toList [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Roi α) : List α :=
  (_root_.Std.Roi.Internal.iter r).ensureTermination.toList

public def Std.Roi.toArray [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Roi α) : Array α :=
  (_root_.Std.Roi.Internal.iter r).ensureTermination.toArray

public def Std.Ric.toList [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Ric α) : List α :=
  (_root_.Std.Ric.Internal.iter r).ensureTermination.toList

public def Std.Ric.toArray [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Ric α) : Array α :=
  (_root_.Std.Ric.Internal.iter r).ensureTermination.toArray

public def Std.Rio.toList [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rio α) : List α :=
  (_root_.Std.Rio.Internal.iter r).ensureTermination.toList

public def Std.Rio.toArray [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rio α) : Array α :=
  (_root_.Std.Rio.Internal.iter r).ensureTermination.toArray

public def Std.Rii.toList [UpwardEnumerable α] [Least? α] (r : Rii α)
    [Iterator (Rxi.Iterator α) Id α] [Finite (Rxi.Iterator α) Id] : List α :=
  (_root_.Std.Rii.Internal.iter r).ensureTermination.toList

public def Std.Rii.toArray {α} [UpwardEnumerable α] [Least? α] (r : Rii α)
    [Iterator (Rxi.Iterator α) Id α] [Finite (Rxi.Iterator α) Id] : Array α :=
  (_root_.Std.Rii.Internal.iter r).ensureTermination.toArray

end OmegaChecks.InitPort.Alternatives
