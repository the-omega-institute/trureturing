module
public import OmegaChecks.InitPort.Alternatives.Collect.ShortCircuit
public import Init.Data.Iterators.Lemmas.Consumers.Access
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Monadic.Basic
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Collect
import all Init.Data.Iterators.Consumers.Total
import all Init.Data.Iterators.Consumers.Loop
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

public theorem Std.IterM.DefaultConsumers.forIn'_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β] {n : Type x → Type x'}
    [Monad n] [LawfulMonad n] {lift : ∀ γ δ, (γ → n δ) → m γ → n δ} {γ : Type x}
    {it : IterM (α := α) m β} {init : γ} {P : β → Prop} {hP : ∀ b, it.IsPlausibleIndirectOutput b → P b}
    (pl : β → γ → ForInStep γ → Prop) {f : (b : β) → P b → (c : γ) → n (Subtype (pl b c))}
    (wf : IteratorLoop.WellFounded α m pl) : type_of% (@IterM.DefaultConsumers.forIn'.wf.eq_def m α β _ n _ lift γ pl wf it init P hP f) :=
  @IterM.DefaultConsumers.forIn'.wf.eq_def m α β _ n _ lift γ pl wf it init P hP f

public theorem Std.IterM.forIn'_eq : type_of% @_root_.Std.IterM.forIn'_eq := by
  intro α β m iter finite n mm mn laws i h liftT lawsT γ it init f
  exact h.lawful (fun _ _ g x => monadLift x >>= g) γ it init (fun _ _ _ => True)
    IteratorLoop.wellFounded_of_finite (fun b p c => do return ⟨← f b p c, trivial⟩)
public theorem Std.IterM.forIn_eq : type_of% @_root_.Std.IterM.forIn_eq := by
  intro α β m iter finite n mm mn laws i h liftT lawsT γ it init f
  exact h.lawful (fun _ _ g x => monadLift x >>= g) γ it init (fun _ _ _ => True)
    IteratorLoop.wellFounded_of_finite (fun b _ c => do return ⟨← f b c, trivial⟩)

public theorem Std.Iter.forIn'_eq : type_of% @_root_.Std.Iter.forIn'_eq := by
  intro α β iter finite m mm laws i h γ it init f
  exact h.lawful (fun _ _ g x => g x.run) γ it.toIterM init (fun _ _ _ => True)
    IteratorLoop.wellFounded_of_finite (fun b p c => do return ⟨← f b (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr p) c, trivial⟩)
public theorem Std.Iter.forIn_eq : type_of% @_root_.Std.Iter.forIn_eq := by
  intro α β iter finite m mm laws i h γ it init f
  exact h.lawful (fun _ _ g x => g x.run) γ it.toIterM init (fun _ _ _ => True)
    IteratorLoop.wellFounded_of_finite (fun b _ c => do return ⟨← f b c, trivial⟩)

private def loopWith {α β : Type w} [Iterator α Id β] [Finite α Id] {γ : Type x}
    (f : β → γ → ForInStep γ) (it : IterM (α := α) Id β) (init : γ)
    (P : β → Prop) (hp : ∀ b, it.IsPlausibleIndirectOutput b → P b) : γ :=
  IterM.DefaultConsumers.forIn'.wf (n := Id) (fun _ _ g x => g x.run) γ (fun _ _ _ => True)
    IteratorLoop.wellFounded_of_finite it init P hp (fun b _ c => ⟨f b c, trivial⟩)

private theorem loopWith_congr {α β : Type w} [Iterator α Id β] [Finite α Id] {γ : Type x}
    (f : β → γ → ForInStep γ) (it : IterM (α := α) Id β) (init : γ)
    (P Q : β → Prop) (hp : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (hq : ∀ b, it.IsPlausibleIndirectOutput b → Q b) :
    loopWith f it init P hp = loopWith f it init Q hq := by
  induction it using IterM.inductSteps generalizing init with
  | step it ihy ihs =>
    unfold loopWith
    rw [IterM.DefaultConsumers.forIn'.wf.eq_def, IterM.DefaultConsumers.forIn'.wf.eq_def]
    dsimp only
    cases it.step.run.inflate using PlausibleIterStep.casesOn with
    | yield next out h =>
      dsimp only [Id.instMonad, bind, pure, Id.run, IterM.Step.toPure, IterStep.mapIterator]
      cases f out init with
      | yield acc => exact ihy h _ _ _
      | done acc => rfl
    | skip next h => exact ihs h _ _ _
    | done h => rfl

private theorem forIn_eq_loopWith {α β : Type w} [Iterator α Id β] [Finite α Id]
    {γ : Type x} [IteratorLoop α Id Id.{x}] [LawfulIteratorLoop α Id Id.{x}]
    (f : β → γ → ForInStep γ) (it : Iter (α := α) β) (init : γ) :
    ForIn.forIn (m := Id) it init f = loopWith f it.toIterM init (fun _ => True) (fun _ _ => trivial) := by
  rw [Iter.forIn_eq, IterM.DefaultConsumers.forIn'_eq_wf (wf := IteratorLoop.wellFounded_of_finite)]
  exact loopWith_congr f it.toIterM init _ _ _ _

private theorem forIn_eq_step {α β : Type w} [Iterator α Id β] [Finite α Id]
    {γ : Type x} [IteratorLoop α Id Id.{x}] [LawfulIteratorLoop α Id Id.{x}]
    (f : β → γ → ForInStep γ) (it : Iter (α := α) β) (init : γ) :
    ForIn.forIn (m := Id) it init f = match it.step.val with
      | .yield next out => match f out init with
        | .yield acc => ForIn.forIn (m := Id) next acc f
        | .done acc => acc
      | .skip next => ForIn.forIn (m := Id) next init f
      | .done => init := by
  rw [forIn_eq_loopWith]
  unfold loopWith
  rw [IterM.DefaultConsumers.forIn'.wf.eq_def]
  dsimp only [Iter.step]
  cases it.toIterM.step.run.inflate using PlausibleIterStep.casesOn with
  | yield next out h =>
    dsimp only [Id.instMonad, bind, pure, Id.run, IterM.Step.toPure, IterStep.mapIterator]
    cases f out init with
    | yield acc => exact (forIn_eq_loopWith f next.toIter acc).symm
    | done acc => rfl
  | skip next h => exact (forIn_eq_loopWith f next.toIter init).symm
  | done h => rfl

public theorem Std.Iter.fold_eq_match_step : type_of% @_root_.Std.Iter.fold_eq_match_step := by
  intro α β γ iter finite loop lawful f init it
  rw [Iter.fold_eq_forIn, forIn_eq_step]
  cases it.step using PlausibleIterStep.casesOn <;> rfl

public theorem Std.Iter.any_eq_match_step : type_of% @_root_.Std.Iter.any_eq_match_step := by
  intro α β iter finite loop laws it p
  rw [Iter.any_eq_forIn]
  rw [forIn_eq_step]
  cases it.step using PlausibleIterStep.casesOn with
  | yield next out h => dsimp only [Id.instMonad, bind, pure, Id.run]; cases p out <;> rfl
  | skip next h => rfl
  | done h => rfl

public theorem Std.Iter.all_eq_match_step : type_of% @_root_.Std.Iter.all_eq_match_step := by
  intro α β iter finite loop laws it p
  rw [Iter.all_eq_forIn]
  rw [forIn_eq_step]
  cases it.step using PlausibleIterStep.casesOn with
  | yield next out h => dsimp only [Id.instMonad, bind, pure, Id.run]; cases p out <;> rfl
  | skip next h => rfl
  | done h => rfl

public theorem Std.Iter.findSome?_eq_match_step : type_of% @_root_.Std.Iter.findSome?_eq_match_step := by
  intro α β γ iter loop finite laws it f
  unfold Iter.findSome? Iter.findSomeM?
  rw [forIn_eq_step]
  cases it.step using PlausibleIterStep.casesOn with
  | yield next out h => dsimp only; cases f out <;> rfl
  | skip next h => rfl
  | done h => rfl

public theorem Std.Iter.findSome?_toList : type_of% @_root_.Std.Iter.findSome?_toList := by
  intro α β γ iter loop finite laws it f
  induction it using Iter.inductSteps with
  | step it ihy ihs =>
    rw [Iter.findSome?_eq_match_step, Iter.toList_eq_match_step]
    cases it.step using PlausibleIterStep.casesOn with
    | yield next out h =>
      dsimp only [List.findSome?]
      cases f out with
      | some _ => rfl
      | none => exact ihy h
    | skip next h => exact ihs h
    | done h => rfl

public theorem Std.Iter.find?_eq_match_step : type_of% @_root_.Std.Iter.find?_eq_match_step := by
  intro α β iter loop finite laws it f
  rw [Iter.find?_eq_findSome?, Iter.findSome?_eq_match_step]
  cases it.step using PlausibleIterStep.casesOn with
  | yield next out h => dsimp only; cases f out <;> rfl
  | skip next h => rfl
  | done h => rfl

private theorem loopWith_pure {α β : Type w} [Iterator α Id β] [Finite α Id]
    {γ : Type x} {m : Type x → Type x'} [Monad m] [LawfulMonad m]
    (g : β → γ → ForInStep γ) (f : β → γ → m (ForInStep γ))
    (h : ∀ b c, f b c = pure (g b c)) (it : IterM (α := α) Id β) (init : γ)
    (P : β → Prop) (hp : ∀ b, it.IsPlausibleIndirectOutput b → P b) :
    IterM.DefaultConsumers.forIn'.wf (n := m) (fun _ _ k x => k x.run) γ (fun _ _ _ => True)
      IteratorLoop.wellFounded_of_finite it init P hp (fun b _ c => do return ⟨← f b c, trivial⟩) =
      pure (loopWith g it init P hp) := by
  induction it using IterM.inductSteps generalizing init with
  | step it ihy ihs =>
    unfold loopWith
    rw [IterM.DefaultConsumers.forIn'.wf.eq_def, IterM.DefaultConsumers.forIn'.wf.eq_def]
    dsimp only
    cases it.step.run.inflate using PlausibleIterStep.casesOn with
    | yield next out hs =>
      dsimp only [Id.instMonad, bind, pure, Id.run]
      rw [h, pure_bind, pure_bind]
      cases g out init with
      | yield acc => exact ihy hs _ _
      | done acc => rfl
    | skip next hs => exact ihs hs _ _
    | done _ => rfl

private theorem forIn_pure {α β : Type w} [Iterator α Id β] [Finite α Id]
    {γ : Type x} {m : Type x → Type x'} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorLoop α Id Id.{x}] [LawfulIteratorLoop α Id Id.{x}]
    (g : β → γ → ForInStep γ) (f : β → γ → m (ForInStep γ))
    (h : ∀ b c, f b c = pure (g b c)) (it : Iter (α := α) β) (init : γ) :
    ForIn.forIn (m := m) it init f = pure (ForIn.forIn (m := Id) it init g) := by
  rw [Iter.forIn_eq, IterM.DefaultConsumers.forIn'_eq_wf (wf := IteratorLoop.wellFounded_of_finite), forIn_eq_loopWith]
  exact (loopWith_pure g f h it.toIterM init _ _).trans (congrArg pure (loopWith_congr g it.toIterM init _ _ _ _))

public theorem Std.Iter.findSomeM?_pure : type_of% @_root_.Std.Iter.findSomeM?_pure := by
  intro α β γ m mon iter lm li laws finite hm hi it f
  unfold Iter.findSome? Iter.findSomeM?
  apply forIn_pure
  intro b c
  rw [pure_bind]
  dsimp only [Id.instMonad, bind, pure, Id.run]
  cases f b <;> rfl

public theorem Std.Iter.findM?_pure : type_of% @_root_.Std.Iter.findM?_pure := by
  intro α β m mon iter lm li laws finite hm hi it f
  unfold Iter.find? Iter.findM? Iter.findSomeM?
  apply forIn_pure
  intro b c
  dsimp only
  rw [pure_bind, pure_bind]
  dsimp only [Id.instMonad, bind, pure, Id.run]
  cases (f b).down <;> rfl

public theorem Std.Iter.length_eq_fold.{w} : type_of% @_root_.Std.Iter.length_eq_fold.{w} := by
  intro α β iter finite i1 h1 i2 h2 it
  rw [Iter.length_eq_length_toIterM, IterM.length_eq_fold, ← Iter.fold_eq_fold_toIterM]
  exact (Iter.fold_hom (it := it) (f := ULift.down)
    (g₁ := fun (n : ULift.{w} Nat) (_ : β) => ULift.up (n.down + 1))
    (g₂ := fun (n : Nat) (_ : β) => n + 1) (init := ULift.up 0) (fun _ _ => rfl)).symm
public theorem Std.Iter.foldl_toList : type_of% @_root_.Std.Iter.foldl_toList := by
  intro α β γ iter finite loop lawful f init it
  induction it using Iter.inductSteps generalizing init with
  | step it ihy ihs =>
    rw [Iter.toList_eq_match_step, Iter.fold_eq_match_step]
    cases it.step using PlausibleIterStep.casesOn
    · apply ihy <;> assumption
    · apply ihs <;> assumption
    · rfl
public theorem Std.Iter.foldl_toArray : type_of% @_root_.Std.Iter.foldl_toArray := by
  intro α β γ iter finite loop lawful f init it
  rw [← Iter.toArray_toList, List.foldl_toArray]
  exact Std.Iter.foldl_toList
public theorem Std.Iter.toList_eq_fold : type_of% @_root_.Std.Iter.toList_eq_fold := by
  intro α β iter finite loop lawful it
  rw [← Std.Iter.foldl_toList]
  rw [List.foldl_append_eq_append, List.nil_append]
  induction it.toList with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

private theorem countFold {β : Type w} (xs : List β) (n : Nat) :
    xs.foldl (fun (a : ULift.{w} Nat) _ => ULift.up (a.down + 1)) (.up n) = .up (n + xs.length) := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    exact (ih (n+1)).trans (congrArg ULift.up ((Nat.succ_add n xs.length).trans (Nat.add_succ n xs.length).symm))
public theorem Std.Iter.length_toList_eq_length.{w} : type_of% @_root_.Std.Iter.length_toList_eq_length.{w} := by
  intro α β iter finite loop lawful it
  rw [Iter.length_eq_length_toIterM, IterM.length_eq_fold, ← Iter.fold_eq_fold_toIterM, ← Std.Iter.foldl_toList]
  exact (Nat.zero_add _).symm.trans (congrArg ULift.down (countFold it.toList 0)).symm
public theorem Std.Iter.length_eq_match_step.{w} : type_of% @_root_.Std.Iter.length_eq_match_step.{w} := by
  intro α β iter finite loop lawful it
  rw [← Std.Iter.length_toList_eq_length, Iter.toList_eq_match_step]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i next out h
    exact congrArg Nat.succ (@Std.Iter.length_toList_eq_length _ _ _ _ _ _ next)
  · rename_i next h
    exact @Std.Iter.length_toList_eq_length _ _ _ _ _ _ next
  · rfl
public theorem Std.Iter.size_toArray_eq_length : type_of% @_root_.Std.Iter.size_toArray_eq_length := by
  intro α β iter finite loop lawful it
  rw [← Iter.toArray_toList, List.size_toArray]
  exact Std.Iter.length_toList_eq_length

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
