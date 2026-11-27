module
public import Init.Data.Iterators.Lemmas.Consumers.Access
import all Init.Data.Iterators.Consumers.Total
public import Init.Data.Iterators.Consumers.Access
import all Init.Data.Iterators.Consumers.Monadic.Loop
public import Init.Data.Slice.Array.Iterator
public import Init.Data.Slice.List.Iterator
public import Init.Data.Iterators.Producers.Monadic.List
/-! Run the default loop by induction on the finite iterator, for arbitrary lifts and monads. -/

open Std Std.Iterators

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.instLawfulIteratorLoopDefaultImplementation :
    type_of% @_root_.Std.instLawfulIteratorLoopDefaultImplementation :=
  fun {β} α m n mm mn iter _ =>
    @_root_.Std.LawfulIteratorLoop.mk β α m n mm mn iter
      (@_root_.Std.IteratorLoop.defaultImplementation β α m n mn iter) (fun _ _ _ _ _ _ _ _ => rfl)

private noncomputable def finiteForIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type x → Type x'} [Monad n] (lift : ∀ γ δ, (γ → n δ) → m γ → n δ)
    (γ : Type x) (Pl : β → γ → ForInStep γ → Prop) (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  let project (p : (i : IterM (α := α) m β) ×' (_ : γ) ×' (∀ b, i.IsPlausibleIndirectOutput b → P b)) :=
    (p.1, p.2.1)
  (InvImage.wf project (IteratorLoop.wellFounded_of_finite (P := Pl))).fix (C := fun _ => n γ)
    (fun p recur => (lift _ _ · p.1.step) fun step => do
      match step.inflate with
      | .yield next out h =>
        match ← f out (p.2.2 out (.direct ⟨_, h⟩)) p.2.1 with
        | ⟨.yield acc, h'⟩ =>
          recur ⟨next, acc, fun _ after => p.2.2 _ (.indirect ⟨_, rfl, h⟩ after)⟩ (Or.inl ⟨out, h, h'⟩)
        | ⟨.done acc, _⟩ => return acc
      | .skip next h =>
        recur ⟨next, p.2.1, fun _ after => p.2.2 _ (.indirect ⟨_, rfl, h⟩ after)⟩ (Or.inr ⟨h, rfl⟩)
      | .done _ => return p.2.1) ⟨it, init, hP⟩

@[instance_reducible] private noncomputable def finiteIteratorLoop {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type x → Type x'} [Monad n] : IteratorLoop α m n where
  forIn lift γ Pl it init := finiteForIn lift γ Pl it init _ (fun _ => id)

@[instance_reducible] public noncomputable def instIteratorLoopSubarrayIteratorIdOfMonad {α : Type u}
    {m : Type v → Type w} [Monad m] : IteratorLoop (SubarrayIterator α) Id m :=
  finiteIteratorLoop

@[instance_reducible] public noncomputable def Std.Iterators.Types.ListIterator.instIteratorLoop :
    type_of% @_root_.Std.Iterators.Types.ListIterator.instIteratorLoop :=
  fun {_ _} _ {_} _ => finiteIteratorLoop

@[instance_reducible] public noncomputable def instForInListSliceOfMonad
    {α : Type u} {m : Type v → Type w} [Monad m] : ForIn m (ListSlice α) α where
  forIn xs init f :=
    @ForIn.forIn m _ α (@Std.instForInIterOfMonadOfIteratorLoopId _ _ m _ _ finiteIteratorLoop)
      _ (Std.Slice.Internal.iter xs) init f

private theorem indexWF {α β : Type u} [Iterator α Id β] [Productive α Id] :
    WellFounded (InvImage (Prod.Lex WellFoundedRelation.rel IterM.TerminationMeasures.Productive.Rel)
      (fun p : (_ : Iter (α := α) β) ×' Nat => (p.2, p.1.finitelyManySkips!))) :=
  InvImage.wf _ WellFoundedRelation.wf

public noncomputable def Std.Iter.Total.atIdxSlow? {α β : Type u} [Iterator α Id β] [Productive α Id]
    (n : Nat) (it : Iter.Total (α := α) β) : Option β :=
  (indexWF (α := α) (β := β)).fix (C := fun _ => Option β) (fun p recur =>
    match p.1.step with
    | .yield next out h =>
      match hIndex : p.2 with
      | 0 => some out
      | k + 1 => recur ⟨next, k⟩ (by
        apply Prod.Lex.left
        change k < p.2
        exact hIndex ▸ Nat.lt_succ_self k)
    | .skip next h => recur ⟨next, p.2⟩ (by
      apply Prod.Lex.right
      exact IterM.TerminationMeasures.Productive.rel_of_skip h)
    | .done _ => none) ⟨it.it, n⟩


private theorem indexEq {α β : Type u} [Iterator α Id β] [Productive α Id]
    {n : Nat} {it : Iter (α := α) β} :
    Std.Iter.Total.atIdxSlow? n it.ensureTermination =
      IterStep.casesOn (motive := fun _ => Option β) it.step.val
        (fun next out => Nat.casesOn n (some out) (fun k => Std.Iter.Total.atIdxSlow? k next.ensureTermination))
        (fun next => Std.Iter.Total.atIdxSlow? n next.ensureTermination) none := by
  conv =>
    lhs
    unfold Std.Iter.Total.atIdxSlow?
    rw [WellFounded.fix_eq]
  dsimp only [Iter.ensureTermination]
  cases it.step using PlausibleIterStep.casesOn with
  | yield next out h => cases n <;> rfl
  | skip next h => rfl
  | done h => rfl

public theorem Std.Iter.atIdxSlow?_eq_match {α β : Type u} [Iterator α Id β] [Productive α Id]
    {n : Nat} {it : Iter (α := α) β} :
    Std.Iter.Total.atIdxSlow? n it.ensureTermination =
      IterStep.casesOn (motive := fun _ => Option β) it.step.val
        (fun next out => Nat.casesOn n (some out) (fun k => Std.Iter.Total.atIdxSlow? k next.ensureTermination))
        (fun next => Std.Iter.Total.atIdxSlow? n next.ensureTermination) none := indexEq


public theorem Std.Iter.atIdxSlow?.induct_unfolding {α β : Type u} [Iterator α Id β] [Productive α Id]
    (motive : Nat → Iter β → Option β → Prop)
    (yield_zero : ∀ (it it' : Iter (α := α) β) (out : β) (property : it.IsPlausibleStep (IterStep.yield it' out)),
        it.step = ⟨IterStep.yield it' out, property⟩ → motive 0 it (some out))
    (yield_succ : ∀ (it it' : Iter (α := α) β) (out : β) (property : it.IsPlausibleStep (IterStep.yield it' out)),
        it.step = ⟨IterStep.yield it' out, property⟩ →
        ∀ (k : Nat), motive k it' (Std.Iter.Total.atIdxSlow? k it'.ensureTermination) → motive k.succ it (Std.Iter.Total.atIdxSlow? k it'.ensureTermination))
    (skip_case : ∀ (n : Nat) (it it' : Iter β) (property : it.IsPlausibleStep (IterStep.skip it')),
        it.step = ⟨IterStep.skip it', property⟩ →
        motive n it' (Std.Iter.Total.atIdxSlow? n it'.ensureTermination) → motive n it (Std.Iter.Total.atIdxSlow? n it'.ensureTermination))
    (done_case : ∀ (n : Nat) (it : Iter β) (property : it.IsPlausibleStep IterStep.done),
        it.step = ⟨IterStep.done, property⟩ → motive n it none)
    (n : Nat) (it : Iter β) : motive n it (Std.Iter.Total.atIdxSlow? n it.ensureTermination) := by
  refine (indexWF (α := α) (β := β)).induction (C := fun p =>
    motive p.2 p.1 (Std.Iter.Total.atIdxSlow? p.2 p.1.ensureTermination)) ⟨it, n⟩ ?_
  rintro ⟨i, k⟩ ih
  change motive k i (Std.Iter.Total.atIdxSlow? k i.ensureTermination)
  rw [indexEq]
  generalize h : i.step = step
  cases step using PlausibleIterStep.casesOn with
  | yield next out hs =>
    cases k with
    | zero => exact yield_zero i next out hs h
    | succ k => exact yield_succ i next out hs h k (ih ⟨next, k⟩ (Prod.Lex.left _ _ (Nat.lt_succ_self k)))
  | skip next hs =>
    exact skip_case k i next hs h (ih ⟨next, k⟩ (Prod.Lex.right _ (IterM.TerminationMeasures.Productive.rel_of_skip hs)))
  | done hs => exact done_case k i hs h

end OmegaChecks.InitPort.Alternatives
