module

public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Iterators.Combinators.Monadic.Take
public import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import all Init.Data.Iterators.Combinators.Monadic.FilterMap
import all Init.Data.Iterators.Consumers.Monadic.Total
import all Init.Data.Iterators.Consumers.Total
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Range.Polymorphic.Map
public import OmegaChecks.InitPort.Alternatives.IteratorSlice
public import OmegaChecks.InitPort.Alternatives.IteratorFilter
public import OmegaChecks.InitPort.Alternatives.FiniteSlice
public import OmegaChecks.InitPort.Alternatives.RangeList

/-! Finite consumers have a well-founded relation in their own interface. -/

open Std Std.PRange Std.Iterators Std.Iterators.Types

namespace OmegaChecks.InitPort.Alternatives

private theorem collectorWF {α β σ : Type u} {m : Type u → Type v}
    [Iterator α m β] [Finite α m] :
    WellFounded (InvImage IterM.TerminationMeasures.Finite.Rel
      (fun p : (_ : IterM (α := α) m β) ×' σ => p.1.finitelyManySteps!)) :=
  InvImage.wf _ (IterM.TerminationMeasures.instWellFoundedRelationFinite (α := α) (m := m)).wf

private noncomputable def collectArrayFrom
    {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m] [Iterator α m β]
    [Finite α m] (it : IterM (α := α) m β) (acc : Array β) : m (Array β) :=
  (collectorWF (α := α) (β := β) (m := m) (σ := Array β)).fix (C := fun _ => m (Array β))
    (fun p recur => do
      match (← p.1.step).inflate with
      | .yield next out h => recur ⟨next, p.2.push out⟩ (IterM.TerminationMeasures.Finite.rel_of_yield h)
      | .skip next h => recur ⟨next, p.2⟩ (IterM.TerminationMeasures.Finite.rel_of_skip h)
      | .done _ => return p.2) ⟨it, acc⟩

public noncomputable def Std.IterM.Total.toArray
    {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m] [Iterator α m β]
    [Finite α m] (it : IterM.Total (α := α) m β) : m (Array β) :=
  collectArrayFrom it.it #[]

private noncomputable def collectRevFrom
    {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m] [Iterator α m β]
    [Finite α m] (it : IterM (α := α) m β) (acc : List β) : m (List β) :=
  (collectorWF (α := α) (β := β) (m := m) (σ := List β)).fix (C := fun _ => m (List β))
    (fun p recur => do
      match (← p.1.step).inflate with
      | .yield next out h => recur ⟨next, out :: p.2⟩ (IterM.TerminationMeasures.Finite.rel_of_yield h)
      | .skip next h => recur ⟨next, p.2⟩ (IterM.TerminationMeasures.Finite.rel_of_skip h)
      | .done _ => return p.2) ⟨it, acc⟩

public noncomputable def Std.IterM.Total.toListRev
    {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m] [Iterator α m β]
    [Finite α m] (it : IterM.Total (α := α) m β) : m (List β) :=
  collectRevFrom it.it []

public noncomputable def Std.IterM.Total.toList {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) : m (List β) :=
  Array.toList <$> Std.IterM.Total.toArray it

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

public theorem Std.Iter.step_filterMapWithPostcondition : type_of% @_root_.Std.Iter.step_filterMapWithPostcondition := by
  intro α β γ inst it m n f mon law lift
  dsimp only [Iter.filterMapWithPostcondition, IterM.filterMapWithPostcondition,
    IterM.InternalCombinators.filterMap, FilterMap.instIterator,
    Iter.step, IterM.step, Iterator.step, Iter.toIterM, monadLift, liftM, Id.run]
  rw [pure_bind]
  generalize Shrink.inflate (Iterator.step { internalState := it.internalState : IterM (α := α) Id β}) = q
  cases q using PlausibleIterStep.casesOn <;> rfl

public theorem Std.Iter.step_map : type_of% @_root_.Std.Iter.step_map := by
  intro α β γ _ it f
  apply Subtype.ext
  unfold Iter.step IterM.step
  dsimp only [Iter.map, IterM.map, IterM.mapWithPostcondition, IterM.InternalCombinators.map,
    Iterators.Types.Map, Iterators.Types.Map.instIterator, Iterators.Types.Map.instIterator._aux_3,
    Iterators.Types.FilterMap.instIterator, IterM.step, Iterator.step,
    Iter.toIterM, IterM.toIter, pure, Bind.bind, monadLift, Id.run] at *
  generalize Shrink.inflate (Iterator.step { internalState := it.internalState : IterM (α := α) Id β}) = q
  cases q using PlausibleIterStep.casesOn <;>
    dsimp only [PostconditionT.map, PostconditionT.pure, bind, pure, Functor.map]
  all_goals
    refine Eq.trans (congrArg (fun s => (IterM.Step.toPure s).val) Shrink.inflate_deflate) ?_
    rfl

public theorem Std.Iter.step_filterMap : type_of% @_root_.Std.Iter.step_filterMap := by
  intro α β γ _ it f
  apply Subtype.ext
  unfold Iter.step IterM.step
  dsimp only [Iter.filterMap, IterM.filterMap, IterM.filterMapWithPostcondition, IterM.InternalCombinators.filterMap,
    Iterators.Types.FilterMap.instIterator, IterM.step, Iterator.step,
    Iter.toIterM, IterM.toIter, pure, Bind.bind, monadLift, Id.run] at *
  generalize Shrink.inflate (Iterator.step { internalState := it.internalState : IterM (α := α) Id β}) = q
  cases q using PlausibleIterStep.casesOn
  case' yield next out h =>
    cases hf : f out <;> dsimp only [PostconditionT.pure, pure] <;> simp only [hf]
  all_goals
    refine Eq.trans (congrArg (fun s => (IterM.Step.toPure s).val) Shrink.inflate_deflate) ?_
    first
    | rfl
    | dsimp only [IterM.Step.toPure, IterStep.mapIterator]
      split <;> rename_i hx <;> cases hf.symm.trans hx <;> rfl

public theorem Std.Iter.val_step_filter : type_of% @_root_.Std.Iter.val_step_filter := by
  intro α β _ it f
  change (it.filterMap (fun b => if f b then some b else none)).step.val = _
  rw [_root_.Std.Iter.val_step_filterMap]
  cases it.step.val with
  | yield next out => dsimp only; cases hf : f out <;> rfl
  | skip _ => rfl
  | done => rfl

public theorem Std.Iter.step_filter : type_of% @_root_.Std.Iter.step_filter := by
  intro α β _ it f
  apply Subtype.ext
  rw [_root_.Std.Iter.val_step_filter]
  cases it.step using PlausibleIterStep.casesOn
  case yield next out h =>
    dsimp only
    by_cases hf : f out = true
    · rw [ite_eq_left hf, dite_eq_left hf]; rfl
    · rw [ite_eq_right hf, dite_eq_right hf]; rfl
  all_goals rfl

public theorem Std.Iter.isPlausibleStep_iff_step_eq : type_of% @_root_.Std.Iter.isPlausibleStep_iff_step_eq := by
  intro α β _ _ _ it step
  obtain ⟨actual, eqStep⟩ := LawfulDeterministicIterator.isPlausibleStep_eq_eq it.toIterM
  constructor
  · intro h
    have chosen := it.step.property
    change it.toIterM.IsPlausibleStep _ at chosen h
    rw [eqStep] at chosen h
    have eq : it.step.val.mapIterator Iter.toIterM = step.mapIterator Iter.toIterM := chosen.trans h.symm
    have cancel (s : IterStep (Iter (α := α) β) β) :
        (s.mapIterator Iter.toIterM).mapIterator IterM.toIter = s := by
      cases s <;> rfl
    exact (cancel _).symm.trans ((congrArg (IterStep.mapIterator IterM.toIter) eq).trans (cancel _))
  · intro h
    exact h ▸ it.step.property

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

section RangeMap

open Std.PRange.UpwardEnumerable
variable {α : Type u} {β : Type v} [UpwardEnumerable α] [UpwardEnumerable β]

public theorem Std.PRange.LawfulUpwardEnumerable.ofMap.{b, a} {α : Type a} {β : Type b}
    [UpwardEnumerable α] [UpwardEnumerable β] [LawfulUpwardEnumerable β] (f : Map α β) :
    LawfulUpwardEnumerable α where
  ne_of_lt a b h eq := LawfulUpwardEnumerable.ne_of_lt _ _ (f.lt_iff.mp h) (congrArg f.toFun eq)
  succMany?_zero a := by
    apply Option.map_injective f.injective
    exact (f.succMany?_toFun _ _).symm.trans (LawfulUpwardEnumerable.succMany?_zero _)
  succMany?_add_one n a := by
    apply Option.map_injective f.injective
    rw [← f.succMany?_toFun, LawfulUpwardEnumerable.succMany?_add_one, f.succMany?_toFun]
    cases heq : succMany? n a with
    | none => rfl
    | some b => exact f.succ?_toFun b

public theorem Std.PRange.instPreservesLTOfLawfulOrderLTOfPreservesLE
    [LE α] [LT α] [LawfulOrderLT α] [LE β] [LT β] [LawfulOrderLT β] (f : Map α β)
    [f.PreservesLE] : f.PreservesLT where
  lt_iff := by
    refine (LawfulOrderLT.lt_iff _ _).trans (Iff.trans ?_ (LawfulOrderLT.lt_iff _ _).symm)
    exact ⟨fun ⟨hab, hnba⟩ => ⟨(Map.PreservesLE.le_iff (f := f)).mp hab,
      fun h => hnba ((Map.PreservesLE.le_iff (f := f)).mpr h)⟩,
      fun ⟨hab, hnba⟩ => ⟨(Map.PreservesLE.le_iff (f := f)).mpr hab,
      fun h => hnba ((Map.PreservesLE.le_iff (f := f)).mp h)⟩⟩

public theorem Std.PRange.LawfulUpwardEnumerableLE.ofMap [LE α] [LE β]
    [LawfulUpwardEnumerableLE β] (f : Map α β) [f.PreservesLE] :
    LawfulUpwardEnumerableLE α where
  le_iff _ _ := (Map.PreservesLE.le_iff (f := f)).trans
    ((LawfulUpwardEnumerableLE.le_iff _ _).trans f.le_iff.symm)

public theorem Std.Rxc.LawfulHasSize.ofMap [LE α] [LE β] [Rxc.HasSize α] [Rxc.HasSize β]
    [Rxc.LawfulHasSize β] (f : Map α β) [f.PreservesLE] [f.PreservesRxcSize] : Rxc.LawfulHasSize α where
  size_eq_zero_of_not_le _ _ h := (Map.PreservesRxcSize.size_eq (f := f)).trans
    (Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ (fun h' => h ((Map.PreservesLE.le_iff (f := f)).mpr h')))
  size_eq_one_of_succ?_eq_none _ _ h hs := (Map.PreservesRxcSize.size_eq (f := f)).trans
    (Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ ((Map.PreservesLE.le_iff (f := f)).mp h)
      (f.succ?_eq_none_iff.mp hs))
  size_eq_succ_of_succ?_eq_some _ _ _ h hs := (Map.PreservesRxcSize.size_eq (f := f)).trans
    ((Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ ((Map.PreservesLE.le_iff (f := f)).mp h)
      (f.succ?_eq_some_iff.mp hs)).trans (congrArg Nat.succ (Map.PreservesRxcSize.size_eq (f := f)).symm))

public theorem Std.Rxc.IsAlwaysFinite.ofMap [LE α] [LE β] [Rxc.IsAlwaysFinite β] (f : Map α β)
    [f.PreservesLE] : Rxc.IsAlwaysFinite α where
  finite lo hi := by
    obtain ⟨n, hn⟩ := Rxc.IsAlwaysFinite.finite (f.toFun lo) (f.toFun hi)
    refine ⟨n, ?_⟩
    rw [f.succMany?_toFun] at hn
    cases hs : succMany? n lo with
    | none => exact True.intro
    | some b =>
      rw [hs] at hn
      exact fun h => hn ((Map.PreservesLE.le_iff (f := f)).mp h)

public theorem Std.PRange.LawfulUpwardEnumerableLT.ofMap [LT α] [LT β]
    [LawfulUpwardEnumerableLT β] (f : Map α β) [f.PreservesLT] :
    LawfulUpwardEnumerableLT α where
  lt_iff _ _ := (Map.PreservesLT.lt_iff (f := f)).trans
    ((LawfulUpwardEnumerableLT.lt_iff _ _).trans f.lt_iff.symm)

public theorem Std.Rxo.LawfulHasSize.ofMap [LT α] [LT β] [Rxo.HasSize α] [Rxo.HasSize β]
    [Rxo.LawfulHasSize β] (f : Map α β) [f.PreservesLT] [f.PreservesRxoSize] : Rxo.LawfulHasSize α where
  size_eq_zero_of_not_le _ _ h := (Map.PreservesRxoSize.size_eq (f := f)).trans
    (Rxo.LawfulHasSize.size_eq_zero_of_not_le _ _ (fun h' => h ((Map.PreservesLT.lt_iff (f := f)).mpr h')))
  size_eq_one_of_succ?_eq_none _ _ h hs := (Map.PreservesRxoSize.size_eq (f := f)).trans
    (Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ ((Map.PreservesLT.lt_iff (f := f)).mp h)
      (f.succ?_eq_none_iff.mp hs))
  size_eq_succ_of_succ?_eq_some _ _ _ h hs := (Map.PreservesRxoSize.size_eq (f := f)).trans
    ((Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ ((Map.PreservesLT.lt_iff (f := f)).mp h)
      (f.succ?_eq_some_iff.mp hs)).trans (congrArg Nat.succ (Map.PreservesRxoSize.size_eq (f := f)).symm))

public theorem Std.Rxo.IsAlwaysFinite.ofMap [LT α] [LT β] [Rxo.IsAlwaysFinite β] (f : Map α β)
    [f.PreservesLT] : Rxo.IsAlwaysFinite α where
  finite lo hi := by
    obtain ⟨n, hn⟩ := Rxo.IsAlwaysFinite.finite (f.toFun lo) (f.toFun hi)
    refine ⟨n, ?_⟩
    rw [f.succMany?_toFun] at hn
    cases hs : succMany? n lo with
    | none => exact True.intro
    | some b =>
      rw [hs] at hn
      exact fun h => hn ((Map.PreservesLT.lt_iff (f := f)).mp h)

public theorem Std.Rxi.LawfulHasSize.ofMap [Rxi.HasSize α] [Rxi.HasSize β] [Rxi.LawfulHasSize β]
    (f : Map α β) [f.PreservesRxiSize] : Rxi.LawfulHasSize α where
  size_eq_one_of_succ?_eq_none _ hs := (Map.PreservesRxiSize.size_eq (f := f)).trans
    (Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _ (f.succ?_eq_none_iff.mp hs))
  size_eq_succ_of_succ?_eq_some _ _ hs := (Map.PreservesRxiSize.size_eq (f := f)).trans
    ((Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ (f.succ?_eq_some_iff.mp hs)).trans
      (congrArg Nat.succ (Map.PreservesRxiSize.size_eq (f := f)).symm))

end RangeMap

variable {α β : Type u} [Iterator α Id β] [Finite α Id]

public def Std.Iter.Total.toArray (it : Iter.Total (α := α) β) : Array β :=
  it.it.toIterM.ensureTermination.toArray.run

public def Std.Iter.Total.toListRev (it : Iter.Total (α := α) β) : List β :=
  it.it.toIterM.ensureTermination.toListRev.run

public noncomputable def Std.Iter.Total.toList (it : Iter.Total (α := α) β) : List β :=
  (Std.IterM.Total.toList it.it.toIterM.ensureTermination).run

public noncomputable def Std.Rcc.toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Rcc α) : List α :=
  Std.Iter.Total.toList (_root_.Std.Rcc.Internal.iter r).ensureTermination

public def Std.Rcc.toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Rcc α) : Array α :=
  (_root_.Std.Rcc.Internal.iter r).ensureTermination.toArray

public noncomputable def Std.Rco.toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rco α) : List α :=
  Std.Iter.Total.toList (_root_.Std.Rco.Internal.iter r).ensureTermination

public def Std.Rco.toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rco α) : Array α :=
  (_root_.Std.Rco.Internal.iter r).ensureTermination.toArray

public def Std.Rci.toList [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Rci α) : List α :=
  (_root_.Std.Rci.Internal.iter r).ensureTermination.toList

public def Std.Rci.toArray [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Rci α) : Array α :=
  (_root_.Std.Rci.Internal.iter r).ensureTermination.toArray

public noncomputable def Std.Roc.toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Roc α) : List α :=
  Std.Iter.Total.toList (_root_.Std.Roc.Internal.iter r).ensureTermination

public def Std.Roc.toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Roc α) : Array α :=
  (_root_.Std.Roc.Internal.iter r).ensureTermination.toArray

public noncomputable def Std.Roo.toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Roo α) : List α :=
  Std.Iter.Total.toList (_root_.Std.Roo.Internal.iter r).ensureTermination

public def Std.Roo.toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Roo α) : Array α :=
  (_root_.Std.Roo.Internal.iter r).ensureTermination.toArray

public def Std.Roi.toList [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Roi α) : List α :=
  (_root_.Std.Roi.Internal.iter r).ensureTermination.toList

public def Std.Roi.toArray [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] (r : Roi α) : Array α :=
  (_root_.Std.Roi.Internal.iter r).ensureTermination.toArray

public noncomputable def Std.Ric.toList [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Ric α) : List α :=
  Std.Iter.Total.toList (_root_.Std.Ric.Internal.iter r).ensureTermination

public def Std.Ric.toArray [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] (r : Ric α) : Array α :=
  (_root_.Std.Ric.Internal.iter r).ensureTermination.toArray

public noncomputable def Std.Rio.toList [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rio α) : List α :=
  Std.Iter.Total.toList (_root_.Std.Rio.Internal.iter r).ensureTermination

public def Std.Rio.toArray [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] (r : Rio α) : Array α :=
  (_root_.Std.Rio.Internal.iter r).ensureTermination.toArray

public def Std.Rii.toList [UpwardEnumerable α] [Least? α] (r : Rii α)
    [Iterator (Rxi.Iterator α) Id α] [Finite (Rxi.Iterator α) Id] : List α :=
  (_root_.Std.Rii.Internal.iter r).ensureTermination.toList

public def Std.Rii.toArray {α} [UpwardEnumerable α] [Least? α] (r : Rii α)
    [Iterator (Rxi.Iterator α) Id α] [Finite (Rxi.Iterator α) Id] : Array α :=
  (_root_.Std.Rii.Internal.iter r).ensureTermination.toArray

private noncomputable def collectInto {α β : Type u} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) (acc : Array β) : Array β :=
  collectArrayFrom it acc

private theorem collectInto_eq {α β : Type u} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) (acc : Array β) :
    collectInto it acc = match it.step.run.inflate with
      | .yield next out _ => collectInto next (acc.push out)
      | .skip next _ => collectInto next acc
      | .done _ => acc := by
  unfold collectInto collectArrayFrom
  rw [WellFounded.fix_eq]
  dsimp only [bind, Id.run]
  cases it.step.inflate using PlausibleIterStep.casesOn <;> rfl

private theorem collectInto_prefix {α β : Type u} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) (pref acc : Array β) :
    collectInto it (pref ++ acc) = pref ++ collectInto it acc := by
  induction it using (Finite.wf (α := α) (m := Id) (β := β)).induction generalizing acc with
  | h it ih =>
    rw [collectInto_eq it (pref ++ acc), collectInto_eq it acc]
    cases it.step.run.inflate using PlausibleIterStep.casesOn with
    | yield next out h =>
      exact (congrArg (collectInto next) (Array.append_push ..).symm).trans
        (ih next (IterM.isPlausibleSuccessorOf_of_yield h) _)
    | skip next h => exact ih next (IterM.isPlausibleSuccessorOf_of_skip h) _
    | done _ => rfl

private theorem collectList_eq {α β : Type u} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) :
    (collectInto it #[]).toList = match it.step.run.inflate.val with
      | .yield next out => out :: (collectInto next #[]).toList
      | .skip next => (collectInto next #[]).toList
      | .done => [] := by
  rw [collectInto_eq it]
  cases it.step.run.inflate using PlausibleIterStep.casesOn with
  | yield next out h =>
    change (collectInto next #[out]).toList = _
    have e := collectInto_prefix next #[out] #[]
    rw [Array.append_empty] at e
    exact (congrArg Array.toList e).trans Array.toList_append
  | skip next h => rfl
  | done _ => rfl


private theorem collectRev_eq {α β : Type u} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) (acc : List β) :
    collectRevFrom it acc = match it.step.run.inflate with
      | .yield next out _ => collectRevFrom next (out :: acc)
      | .skip next _ => collectRevFrom next acc
      | .done _ => acc := by
  unfold collectRevFrom
  rw [WellFounded.fix_eq]
  dsimp only [bind, Id.run]
  cases it.step.inflate using PlausibleIterStep.casesOn <;> rfl

private theorem collectRev_acc {α β : Type u} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) (acc : List β) :
    collectRevFrom it acc = (collectInto it #[]).toList.reverse ++ acc := by
  induction it using (Finite.wf (α := α) (m := Id) (β := β)).induction generalizing acc with
  | h it ih =>
    rw [collectRev_eq, collectList_eq]
    cases it.step.run.inflate using PlausibleIterStep.casesOn with
    | yield next out plausible =>
      rw [List.reverse_cons, List.append_assoc]
      exact ih next (IterM.isPlausibleSuccessorOf_of_yield plausible) _
    | skip next plausible => exact ih next (IterM.isPlausibleSuccessorOf_of_skip plausible) _
    | done _ => rfl

public theorem Std.Iter.toListRev_eq {α β : Type u} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    Std.IterM.Total.toListRev it.toIterM.ensureTermination =
      (Std.IterM.Total.toList it.toIterM.ensureTermination).run.reverse := by
  change collectRevFrom it.toIterM [] = (collectInto it.toIterM #[]).toList.reverse
  exact (collectRev_acc it.toIterM []).trans (List.append_nil _)

public theorem Std.Iter.toList_eq_match_step {α β : Type u} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    Std.Iter.Total.toList it.ensureTermination =
      IterStep.casesOn (motive := fun _ => List β) it.step.val
        (fun next out => out :: Std.Iter.Total.toList next.ensureTermination)
        (fun next => Std.Iter.Total.toList next.ensureTermination) [] := by
  change (collectInto it.toIterM #[]).toList = _
  rw [collectList_eq]
  unfold _root_.Std.Iter.step
  cases it.toIterM.step.run.inflate using PlausibleIterStep.casesOn <;> rfl

public theorem Std.Iter.toList_eq_toList_toIterM {α β : Type u} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    Std.Iter.Total.toList it.ensureTermination = (Std.IterM.Total.toList it.toIterM.ensureTermination).run := (rfl)

public theorem Std.IterM.toList_toIter {α β : Type u} [Iterator α Id β] [Finite α Id]
    {it : IterM (α := α) Id β} :
    Std.Iter.Total.toList it.toIter.ensureTermination = (Std.IterM.Total.toList it.ensureTermination).run := (rfl)

public theorem Std.Iter.toList_map : type_of% @_root_.Std.Iter.toList_map := by
  intro α β γ iterator it finite f
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Iter.toList_eq_match_step (it := it.map f),
      _root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Iter.step_map]
    cases it.step using PlausibleIterStep.casesOn with
    | yield next out h => exact congrArg (List.cons (f out)) (ihy h)
    | skip next h => exact ihs h
    | done _ => rfl

private theorem realStepRxo {α : Type u} [UpwardEnumerable α] [LT α] [DecidableLT α] (it : IterM (α := Rxo.Iterator α) Id α) : it.step.run.inflate.val = Rxo.Iterator.Monadic.step it :=
    congrArg Subtype.val (Shrink.inflate_deflate (x := ⟨Rxo.Iterator.Monadic.step it, rfl⟩) (α := PlausibleIterStep it.IsPlausibleStep))

private theorem realStepRxc {α : Type u} [UpwardEnumerable α] [LE α] [DecidableLE α] (it : IterM (α := Rxc.Iterator α) Id α) : it.step.run.inflate.val = Rxc.Iterator.Monadic.step it :=
    congrArg Subtype.val (Shrink.inflate_deflate (x := ⟨Rxc.Iterator.Monadic.step it, rfl⟩) (α := PlausibleIterStep it.IsPlausibleStep))

public theorem Std.Rco.toList_eq_ite_roo {α : Type u} {r : Rco α} [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerableLT α] :
    OmegaChecks.InitPort.Alternatives.Std.Rco.toList r = if r.lower < r.upper then r.lower :: Std.Roo.toList ⟨r.lower, r.upper⟩ else [] := by
  change (collectInto (_root_.Std.Rco.Internal.iter r).toIterM #[]).toList = _
  rw [collectList_eq]
  rw [realStepRxo]
  dsimp only [Rxo.Iterator.Monadic.step, _root_.Std.Rco.Internal.iter, Iter.toIterM]
  by_cases hw : r.lower < r.upper
  · rw [ite_eq_left hw, ite_eq_left hw]
    rfl
  · rw [ite_eq_right hw, ite_eq_right hw]

public theorem Std.Rcc.toList_eq_ite_roc {α : Type u} {r : Rcc α} [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] :
    OmegaChecks.InitPort.Alternatives.Std.Rcc.toList r = if r.lower ≤ r.upper then r.lower :: Std.Roc.toList ⟨r.lower, r.upper⟩ else [] := by
  change (collectInto (_root_.Std.Rcc.Internal.iter r).toIterM #[]).toList = _
  rw [collectList_eq]
  rw [realStepRxc]
  dsimp only [Rxc.Iterator.Monadic.step, _root_.Std.Rcc.Internal.iter, Iter.toIterM]
  by_cases hw : r.lower ≤ r.upper
  · rw [ite_eq_left hw, ite_eq_left hw]
    rfl
  · rw [ite_eq_right hw, ite_eq_right hw]

public theorem Std.Roo.toList_eq_match_rco {α : Type u} {r : Roo α} [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] :
    Std.Roo.toList r = (UpwardEnumerable.succ? r.lower).elim [] (fun next => Std.Rco.toList ⟨next, r.upper⟩) := by
  change (collectInto (_root_.Std.Roo.Internal.iter r).toIterM #[]).toList = _
  dsimp only [_root_.Std.Roo.Internal.iter, Iter.toIterM]
  cases hn : UpwardEnumerable.succ? r.lower with
  | none =>
    rw [collectList_eq]
    rw [realStepRxo]
    rfl
  | some next => rfl

public theorem Std.Roc.toList_eq_match_rcc {α : Type u} {r : Roc α} [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] :
    Std.Roc.toList r = (UpwardEnumerable.succ? r.lower).elim [] (fun next => Std.Rcc.toList ⟨next, r.upper⟩) := by
  change (collectInto (_root_.Std.Roc.Internal.iter r).toIterM #[]).toList = _
  dsimp only [_root_.Std.Roc.Internal.iter, Iter.toIterM]
  cases hn : UpwardEnumerable.succ? r.lower with
  | none =>
    rw [collectList_eq]
    rw [realStepRxc]
    rfl
  | some next => rfl

public theorem Std.Ric.toList_eq_match_rcc {α : Type u} {r : Ric α} [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] :
    Std.Ric.toList r = (Least?.least? (α := α)).elim [] (fun next => Std.Rcc.toList ⟨next, r.upper⟩) := by
  change (collectInto (_root_.Std.Ric.Internal.iter r).toIterM #[]).toList = _
  dsimp only [_root_.Std.Ric.Internal.iter, Iter.toIterM]
  cases hn : Least?.least? (α := α) with
  | none =>
    rw [collectList_eq]
    rw [realStepRxc]
    rfl
  | some next => rfl

public theorem Std.Rio.toList_eq_match_rco {α : Type u} {r : Rio α} [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] :
    Std.Rio.toList r = (Least?.least? (α := α)).elim [] (fun next => Std.Rco.toList ⟨next, r.upper⟩) := by
  change (collectInto (_root_.Std.Rio.Internal.iter r).toIterM #[]).toList = _
  dsimp only [_root_.Std.Rio.Internal.iter, Iter.toIterM]
  cases hn : Least?.least? (α := α) with
  | none =>
    rw [collectList_eq]
    rw [realStepRxo]
    rfl
  | some next => rfl

public theorem Std.Iter.mem_toList_iff_isPlausibleIndirectOutput :
    type_of% @_root_.Std.Iter.mem_toList_iff_isPlausibleIndirectOutput := by
  intro α β _ _ _ it out
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Iter.toList_eq_match_step]
    constructor
    · intro member
      cases heq : it.step using PlausibleIterStep.casesOn with
      | yield next value plausible =>
        rw [heq] at member
        rcases List.mem_cons.mp member with rfl | tail
        · exact .direct (Iter.isPlausibleOutput_iff_exists.mpr ⟨next, plausible⟩)
        · exact .indirect (Iter.isPlausibleSuccessorOf_iff_exists.mpr ⟨_, rfl, plausible⟩) ((ihy plausible).mp tail)
      | skip next plausible =>
        rw [heq] at member
        exact .indirect (Iter.isPlausibleSuccessorOf_iff_exists.mpr ⟨_, rfl, plausible⟩) ((ihs plausible).mp member)
      | done _ =>
        rw [heq] at member
        cases member
    · intro reachable
      cases reachable with
      | direct output =>
        obtain ⟨next, step⟩ := Iter.isPlausibleOutput_iff_exists.mp output
        rw [Iter.isPlausibleStep_iff_step_eq.mp step]
        exact .head _
      | indirect link tail =>
        obtain ⟨step, toNext, plausible⟩ := Iter.isPlausibleSuccessorOf_iff_exists.mp link
        rw [Iter.isPlausibleStep_iff_step_eq.mp plausible]
        cases step with
        | yield next value =>
          cases Option.some.inj toNext
          exact .tail _ ((ihy plausible).mpr tail)
        | skip next =>
          cases Option.some.inj toNext
          exact (ihs plausible).mpr tail
        | done => cases toNext

public theorem Std.Iter.getElem?_toList_eq_atIdxSlow? {α β : Type u} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} {k : Nat} :
    (Std.Iter.Total.toList it.ensureTermination)[k]? = Std.Iter.Total.atIdxSlow? k it.ensureTermination := by
  induction it using _root_.Std.Iter.inductSteps generalizing k with
  | step it ihy ihs =>
    rw [Std.Iter.toList_eq_match_step, Std.Iter.atIdxSlow?_eq_match]
    cases it.step using PlausibleIterStep.casesOn with
    | yield next out h => cases k with
      | zero => rfl
      | succ k => exact ihy h
    | skip next h => exact ihs h
    | done h => exact List.getElem?_nil

public theorem Std.Iter.toList_eq_of_atIdxSlow?_eq {α₁ α₂ β : Type u}
    [Iterator α₁ Id β] [Finite α₁ Id] [Iterator α₂ Id β] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β}
    (h : ∀ k, Std.Iter.Total.atIdxSlow? k it₁.ensureTermination = Std.Iter.Total.atIdxSlow? k it₂.ensureTermination) :
    Std.Iter.Total.toList it₁.ensureTermination = Std.Iter.Total.toList it₂.ensureTermination := by
  apply List.ext_getElem?
  intro k
  exact (Std.Iter.getElem?_toList_eq_atIdxSlow? (it := it₁)).trans
    ((h k).trans (Std.Iter.getElem?_toList_eq_atIdxSlow? (it := it₂)).symm)

end OmegaChecks.InitPort.Alternatives
