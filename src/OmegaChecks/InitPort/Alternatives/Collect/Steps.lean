module

import all Init.Data.Iterators.Combinators.Monadic.Take
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.Take
import all Init.Data.Iterators.Lemmas.Combinators.Monadic.Take
public import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import all Init.Data.Iterators.Lemmas.Combinators.FilterMap
import all Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
import all Init.Data.Iterators.Combinators.Monadic.FilterMap

/-! Steps and termination measures for iterator combinators. -/

open Std Std.Iterators Std.Iterators.Types

namespace OmegaChecks.InitPort.Alternatives

/-- A decreasing countdown suffices. At equal countdowns, a finite inner iterator
also allows yielding steps to contribute to the decrease. The pinned Take.Rel.eq_1
selects its branch with a finiteness decision. Even on productive natural-number
iterators, its Boolean tag on bounded program simulations decides halting
(Collector.not_computable_take_finiteness_bit). -/
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

/-- At equal countdowns, use skip induction until an edge supplies finiteness of the inner iterator. -/
public theorem Std.Iterators.Types.Take.instFinitenessRelation._proof_1 {α : Type u} {m : Type u → Type v}
    {β : Type u} [Monad m] [Iterator α m β] [Productive α m] :
    WellFounded (Std.Iterators.Types.Take.Rel (α := α) (β := β) m) := by
  let Inner := IterM (α := α) m β
  let skipRel := fun (a b : Inner) => a.finitelyManySkips.Rel b.finitelyManySkips
  let stepRel := fun (a b : Inner) => a.finitelyManySteps!.Rel b.finitelyManySteps!
  let innerRel := fun (a b : Inner) => skipRel a b ∨ Finite α m ∧ stepRel a b
  have accFinite (hf : Finite α m) : WellFounded innerRel :=
    Subrelation.wf (r := stepRel) (fun {_ _} h => h.elim (fun hs => .of_productive hs) (·.2))
      (InvImage.wf (fun t : Inner => t.finitelyManySteps) WellFoundedRelation.wf)
  have skips : WellFounded skipRel := InvImage.wf (fun t : Inner => t.finitelyManySkips) WellFoundedRelation.wf
  have combined : WellFounded innerRel := by
    constructor
    intro a
    induction a using skips.induction with
    | h a ih =>
      constructor
      intro b edge
      exact edge.elim (ih b) (fun h => (accFinite h.1).apply b)
  let rank := fun t : IterM (α := Take α m) m β => (t.internalState.countdown, t.internalState.inner)
  refine Subrelation.wf (r := InvImage (Prod.Lex Nat.lt innerRel) rank) ?_
    (InvImage.wf _ (Prod.lex Nat.lt_wfRel ⟨innerRel, combined⟩).wf)
  intro a b e
  rcases e with dec | ⟨eqCount, inner⟩
  · exact Prod.Lex.left _ _ dec
  · rcases a with ⟨⟨ac, ai, af⟩⟩
    rcases b with ⟨⟨bc, bi, bf⟩⟩
    cases eqCount
    exact Prod.Lex.right _ inner

public theorem Std.IterM.step_take : type_of% @_root_.Std.IterM.step_take := by
  intro α m β mon inst n it
  cases n with
  | zero => rfl
  | succ k =>
    dsimp only [IterM.take, IterM.step, Iterator.step, IterM.internalState_mk, Take.instIterator]
    rw [dite_eq_right (fun h => Nat.noConfusion (Nat.succ.inj h))]
    congr 1
    unfold Take.instIterator.match_1 _root_.Std.IterM.step_take.match_1
    rfl

public theorem Std.Iter.step_filterMapWithPostcondition : type_of% @_root_.Std.Iter.step_filterMapWithPostcondition := by
  intro α β γ inst it m n f mon law lift
  dsimp only [Iter.filterMapWithPostcondition, IterM.filterMapWithPostcondition,
    IterM.InternalCombinators.filterMap, FilterMap.instIterator,
    Iter.step, IterM.step, Iterator.step, Iter.toIterM, monadLift, liftM, Id.run]
  rw [pure_bind]
  generalize Shrink.inflate (Iterator.step { internalState := it.internalState : IterM (α := α) Id β}) = q
  cases q using PlausibleIterStep.casesOn <;> rfl

public theorem Std.Iter.step_filterMapM : type_of% @_root_.Std.Iter.step_filterMapM := by
  intro α β inst it m n γ f mon att law lift
  letI : MonadLift Id n := ⟨pure⟩
  refine (_root_.Std.IterM.step_filterMapM (it := it.toIterM) (f := f)).trans ?_
  dsimp only [Iter.step, liftM, monadLift, Id.run]
  rw [pure_bind]
  generalize it.toIterM.step.inflate = q
  cases q using PlausibleIterStep.casesOn <;> try rfl
  dsimp only [IterM.Step.toPure, IterStep.mapIterator]
  congr 1
  unfold _root_.Std.IterM.step_filterMapM.match_1 _root_.Std.Iter.step_filterMapM.match_1
  rfl

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

end OmegaChecks.InitPort.Alternatives
