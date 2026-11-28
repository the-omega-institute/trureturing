/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
public import Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Iterators.Consumers.Loop

/-! Finite polymorphic ranges admit the optimized official iteration using their proof of well-foundedness. -/

open Std Std.Iterators Std.PRange
namespace OmegaChecks.InitPort.Alternatives

private noncomputable def finiteFix₃ {α : Sort u} {β : α → Sort v} {δ : (a : α) → β a → Sort w}
    {C₃ : (a : α) → (b : β a) → δ a b → Sort x}
    {R : (a : α) ×' (b : β a) ×' δ a b → (a : α) ×' (b : β a) ×' δ a b → Prop}
    (wf : WellFounded R)
    (F : ∀ a b c, (∀ a' b' c', R ⟨a', b', c'⟩ ⟨a, b, c⟩ → C₃ a' b' c') → C₃ a b c)
    (a b c) : C₃ a b c :=
  wf.fix (C := fun p => C₃ p.1 p.2.1 p.2.2)
    (fun p rec => F p.1 p.2.1 p.2.2 (fun a b c => rec ⟨a, b, c⟩)) ⟨a, b, c⟩

variable {α : Type u}

@[instance_reducible] private noncomputable def finiteRxcLoop [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] [Finite (Rxc.Iterator α) Id] :
    IteratorLoop (Rxc.Iterator α) Id n where
  forIn _ γ Pl it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      loop γ Pl (next ≤ ·) (fun a b hab hna => ?hle) upperBound init next ?hle'' (fun a ha₁ ha₂ c => f a ?hf c)
    | ⟨⟨none, _⟩⟩ => return init
  where
    loop γ (Pl : α → γ → ForInStep γ → Prop) (LargeEnough : α → Prop) (hl : ∀ a b : α, a ≤ b → LargeEnough a → LargeEnough b)
        (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
        (f : (out : α) → LargeEnough out → out ≤ upperBound → (c : γ) → n (Subtype (Pl out c))) : n γ :=
      finiteFix₃ (C₃ := fun _ _ _ => n γ)
        (InvImage.wf (fun x => (⟨Rxc.Iterator.mk (some x.1) upperBound⟩, x.2.1)) (IteratorLoop.wellFounded_of_finite (m := Id) (P := Pl)))
        (fun next acc (h : LargeEnough next) G => do
          if hu : next ≤ upperBound then
            match ← f next h hu acc with
            | ⟨.yield acc', h'⟩ =>
              match hs : UpwardEnumerable.succ? next with
              | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
              | none => return acc'
            | ⟨.done acc', _⟩ => return acc'
          else
            return acc) next acc h
  finally
    case hf =>
      apply _root_.Std.Rxc.Iterator.Monadic.isPlausibleIndirectOutput_iff.mpr
      obtain ⟨n, hn⟩ := UpwardEnumerable.le_iff.mp ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_trans
        (UpwardEnumerable.le_iff.mp hna) (UpwardEnumerable.le_iff.mp hab))
    case hle' =>
      apply UpwardEnumerable.le_iff.mpr
      refine ⟨1, ?_⟩
      exact succMany?_one.trans hs
    case hle'' =>
      exact UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl _)
    case decreasing =>
      refine Or.inl ⟨next, ?_, h'⟩
      apply _root_.Std.Rxc.Iterator.Monadic.isPlausibleStep_iff.mpr
      unfold _root_.Std.Rxc.Iterator.Monadic.step
      dsimp only
      rw [ite_eq_left hu, hs]

@[instance_reducible] private noncomputable def finiteRxoLoop [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] [Finite (Rxo.Iterator α) Id] :
    IteratorLoop (Rxo.Iterator α) Id n where
  forIn _ γ Pl it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      loop γ Pl (UpwardEnumerable.LE next ·) (fun a b hab hna => ?hle) upperBound init next ?hle'' (fun a ha₁ ha₂ c => f a ?hf c)
    | ⟨⟨none, _⟩⟩ => return init
  where
    loop γ (Pl : α → γ → ForInStep γ → Prop) (LargeEnough : α → Prop)
        (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
        (upperBound : α) (acc : γ) (next : α) (h : LargeEnough next)
        (f : (out : α) → LargeEnough out → out < upperBound → (c : γ) → n (Subtype (Pl out c))) : n γ :=
      finiteFix₃ (C₃ := fun _ _ _ => n γ)
        (InvImage.wf (fun x => (⟨Rxo.Iterator.mk (some x.1) upperBound⟩, x.2.1)) (IteratorLoop.wellFounded_of_finite (m := Id) (P := Pl)))
        (fun next acc (h : LargeEnough next) G => do
          if hu : next < upperBound then
            match ← f next h hu acc with
            | ⟨.yield acc', h'⟩ =>
              match hs : UpwardEnumerable.succ? next with
              | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
              | none => return acc'
            | ⟨.done acc', _⟩ => return acc'
          else
            return acc) next acc h
  finally
    case hf =>
      apply _root_.Std.Rxo.Iterator.Monadic.isPlausibleIndirectOutput_iff.mpr
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_trans hna hab
    case hle' =>
      refine ⟨1, ?_⟩
      exact succMany?_one.trans hs
    case hle'' =>
      exact UpwardEnumerable.le_refl _
    case decreasing =>
      refine Or.inl ⟨next, ?_, h'⟩
      apply _root_.Std.Rxo.Iterator.Monadic.isPlausibleStep_iff.mpr
      unfold _root_.Std.Rxo.Iterator.Monadic.step
      dsimp only
      rw [ite_eq_left hu, hs]

@[instance_reducible] private noncomputable def finiteRxiLoop [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {n : Type u → Type w} [Monad n] [Finite (Rxi.Iterator α) Id] :
    IteratorLoop (Rxi.Iterator α) Id n where
  forIn _ γ Pl it init f :=
    match it with
    | ⟨⟨some next⟩⟩ =>
      loop γ Pl (UpwardEnumerable.LE next ·) (fun a b hab hna => ?hle) init next ?hle'' (fun a ha c => f a ?hf c)
    | ⟨⟨none⟩⟩ => return init
  where
    loop γ (Pl : α → γ → ForInStep γ → Prop) (LargeEnough : α → Prop) (hl : ∀ a b : α, UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b)
        (acc : γ) (next : α) (h : LargeEnough next)
        (f : (out : α) → LargeEnough out → (c : γ) → n (Subtype (Pl out c))) : n γ :=
      finiteFix₃ (C₃ := fun _ _ _ => n γ)
        (InvImage.wf (fun x => (⟨Rxi.Iterator.mk (some x.1)⟩, x.2.1)) (IteratorLoop.wellFounded_of_finite (m := Id) (P := Pl)))
        (fun next acc (h : LargeEnough next) G => do
          match ← f next h acc with
          | ⟨.yield acc', h'⟩ =>
            match hs : UpwardEnumerable.succ? next with
            | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
            | none => return acc'
          | ⟨.done acc', _⟩ => return acc') next acc h
  finally
    case hf =>
      apply _root_.Std.Rxi.Iterator.Monadic.isPlausibleIndirectOutput_iff.mpr
      exact ha
    case hle =>
      exact UpwardEnumerable.le_trans hna hab
    case hle' =>
      refine ⟨1, ?_⟩
      exact succMany?_one.trans hs
    case hle'' =>
      exact UpwardEnumerable.le_refl _
    case decreasing =>
      refine Or.inl ⟨next, ?_, h'⟩
      apply _root_.Std.Rxi.Iterator.Monadic.isPlausibleStep_iff.mpr
      unfold _root_.Std.Rxi.Iterator.Monadic.step
      dsimp only
      rw [hs]

/-- A reachable inclusive upper endpoint has no later successor inside the range. -/
private theorem closedFinite {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerableLE α] : Rxc.IsAlwaysFinite α where
  finite lo hi := by
    by_cases inside : lo ≤ hi
    · obtain ⟨n, reach⟩ := UpwardEnumerable.le_iff.mp inside
      refine ⟨n + 1, ?_⟩
      rw [succMany?_add_one, reach, Option.bind_some]
      cases step : UpwardEnumerable.succ? hi with
      | none => exact True.intro
      | some after => exact fun le =>
          UpwardEnumerable.not_ge_of_lt (UpwardEnumerable.lt_succ? step) (UpwardEnumerable.le_iff.mp le)
    · exact ⟨0, by rw [succMany?_zero]; exact inside⟩

/-- The witness for the strict comparison reaches the first excluded endpoint. -/
private theorem openFinite {α : Type u} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LT α] [DecidableLT α] [LawfulUpwardEnumerableLT α] : Rxo.IsAlwaysFinite α where
  finite lo hi := by
    by_cases inside : lo < hi
    · obtain ⟨n, reach⟩ := UpwardEnumerable.lt_iff.mp inside
      exact ⟨n + 1, by rw [reach]; exact fun lt => UpwardEnumerable.lt_irrefl (UpwardEnumerable.lt_iff.mp lt)⟩
    · exact ⟨0, by rw [succMany?_zero]; exact inside⟩

private noncomputable def finiteClosedRangeLoop :
    type_of% @_root_.Std.Rxc.Iterator.instIteratorLoop.loop := by
  intro α enum order dec law compat n mon
  letI := closedFinite (α := α)
  exact finiteRxcLoop.loop

/-- Unfold an entire family of well-founded calls by supplying an explicit accessibility constructor. -/
private theorem unfoldFamily {A : Sort u} {R : A → A → Prop} {C : A → Sort v}
    (wf : WellFounded R) (step : ∀ x, (∀ y, R y x → C y) → C x) {I : Sort w} (atIndex : I → A) :
    (fun i => wf.fix step (atIndex i)) =
      fun i => step (atIndex i) (fun y _ => wf.fix step y) := by
  calc
    _ = fun i => WellFounded.fixF step (atIndex i)
          (Acc.intro (atIndex i) (fun y _ => wf.apply y)) := rfl
    _ = _ := rfl

private theorem falseFamily {γ : Type u} {A : Sort v} {p : Prop} [d : Decidable p] (outside : ¬ p)
    (yes : γ → p → A) (no : γ → ¬p → A) :
    (fun c => if h : p then yes c h else no c h) = (fun c => no c outside) := by
  cases d with
  | isTrue h => exact (outside h).elim
  | isFalse _ => rfl

private theorem trueFamily {γ : Type u} {A : Sort v} {p : Prop} [d : Decidable p] (inside : p)
    (yes : γ → p → A) (no : γ → ¬p → A) :
    (fun c => if h : p then yes c h else no c h) = (fun c => yes c inside) := by
  cases d with
  | isTrue h => rfl
  | isFalse h => exact (h inside).elim

private def resumeLoop {α γ : Type u} {m : Type u → Type v} [Monad m]
    (s : Option α) (rec : (y : α) → s = some y → γ → m γ) (c : γ) : m γ :=
  finiteRxcLoop.loop.match_1 (fun _ => m γ) s (fun y hs => rec y hs c) (fun _ => pure c)

private theorem resumeCongr {α γ : Type u} {m : Type u → Type v} [Monad m]
    (s : Option α) (l r : (y : α) → s = some y → γ → m γ)
    (h : ∀ y e, l y e = r y e) : resumeLoop s l = resumeLoop s r := by
  cases s with
  | none => rfl
  | some y => exact h y rfl

/-- Induct on the distance to an excluded endpoint. Equality as functions of the accumulator
lets each monadic bind use the same continuation on both sides. -/
private theorem rangeDecisions {α : Type u} [enum : UpwardEnumerable α] [le : LE α]
    (d₁ d₂ : DecidableLE α) [law : LawfulUpwardEnumerable α] [compat : LawfulUpwardEnumerableLE α]
    {m : Type u → Type w} [mon : Monad m] (γ : Type u) (Pl : α → γ → ForInStep γ → Prop)
    (P : α → Prop) (hp : ∀ a b, a ≤ b → P a → P b) (upper : α)
    (f : (out : α) → P out → out ≤ upper → (acc : γ) → m (Subtype (Pl out acc))) :
    ∀ k next (h : P next), (succMany? k next).elim True (fun y => ¬ y ≤ upper) →
      (fun c => @finiteClosedRangeLoop α enum le d₁ law compat m mon γ Pl P hp upper c next h f) =
      (fun c => @finiteClosedRangeLoop α enum le d₂ law compat m mon γ Pl P hp upper c next h f) := by
  letI : DecidableLE α := d₁
  intro k
  induction k with
  | zero =>
    intro next hn stop
    rw [succMany?_zero] at stop
    have outside : ¬ next ≤ upper := stop
    unfold finiteClosedRangeLoop finiteRxcLoop.loop finiteFix₃
    rw [unfoldFamily, unfoldFamily]
    dsimp only
    calc
      _ = (fun c : γ => pure (f := m) c) := by apply @falseFamily _ _ _ (d₁ next upper) outside
      _ = _ := by symm; apply @falseFamily _ _ _ (d₂ next upper) outside
  | succ k ih =>
    intro next hn stop
    by_cases inside : next ≤ upper
    · have later (y : α) (hs : succ? next = some y) : P y :=
        hp next y (UpwardEnumerable.le_iff.mpr ⟨1, succMany?_one.trans hs⟩) hn
      let after (d : DecidableLE α) (y : α) (hs : succ? next = some y) (c : γ) :=
        @finiteClosedRangeLoop α enum le d law compat m mon γ Pl P hp upper c y (later y hs) f
      have tails := resumeCongr (succ? next) (after d₁) (after d₂) (fun y hs =>
        ih y (later y hs) (by rwa [succMany?_add_one_eq_succ?_bind_succMany?, hs, Option.bind_some] at stop))
      unfold finiteClosedRangeLoop finiteRxcLoop.loop finiteFix₃
      rw [unfoldFamily, unfoldFamily]
      dsimp only
      rw [@trueFamily _ _ _ (d₁ next upper) inside, @trueFamily _ _ _ (d₂ next upper) inside]
      exact congrArg (fun (resume : γ → m γ) => fun c => do
        let step ← f next hn inside c
        finiteRxcLoop.loop.match_3 γ Pl next c (fun _ => m γ) step
          (fun c' _ => resume c') (fun c' _ => pure c')) tails
    · unfold finiteClosedRangeLoop finiteRxcLoop.loop finiteFix₃
      rw [unfoldFamily, unfoldFamily]
      dsimp only
      calc
        _ = (fun c : γ => pure (f := m) c) := by apply @falseFamily _ _ _ (d₁ next upper) inside
        _ = _ := by symm; apply @falseFamily _ _ _ (d₂ next upper) inside

private theorem closedRangeCongr
    {α : Type u} [enum : UpwardEnumerable α] [le : LE α] {d₁ : DecidableLE α} [d₂ : DecidableLE α]
    [law : LawfulUpwardEnumerable α] [compat : LawfulUpwardEnumerableLE α]
    {m : Type u → Type w} [mon : Monad m] (γ : Type u) (Pl : α → γ → ForInStep γ → Prop)
    (P : α → Prop) (hp : ∀ a b, a ≤ b → P a → P b) (upper : α)
    (acc acc' : γ) (e_acc : acc = acc') (next next' : α) (e_next : next = next') (h : P next)
    (f f' : (out : α) → P out → out ≤ upper → (c : γ) → m (Subtype (Pl out c))) (e_f : f = f') :
    @finiteClosedRangeLoop α enum le d₁ law compat m mon γ Pl P hp upper acc next h f =
      @finiteClosedRangeLoop α enum le d₂ law compat m mon γ Pl P hp upper acc' next' (e_next ▸ h) f' := by
  cases e_acc
  cases e_next
  cases e_f
  obtain ⟨k, stop⟩ := (closedFinite (α := α)).finite next upper
  exact congrFun (rangeDecisions d₁ d₂ γ Pl P hp upper f k next h stop) acc

-- Declare the congruence first, while the implementation name is still available.
public theorem Std.Rxc.Iterator.instIteratorLoop.loop.congr_simp :
    type_of% (private_decl% @closedRangeCongr) := @closedRangeCongr

-- The pinned loop.eq_1 right endpoint names WellFounded.extrinsicFix₃.
-- The finite loop implementation below supplies a different recursion operator.
public noncomputable def Std.Rxc.Iterator.instIteratorLoop.loop :
    type_of% @_root_.Std.Rxc.Iterator.instIteratorLoop.loop := by
  intro α enum order dec law compat n mon
  letI := closedFinite (α := α)
  exact finiteRxcLoop.loop

@[instance_reducible] public noncomputable def Std.Rxo.Iterator.instIteratorLoop
    [UpwardEnumerable α] [LT α] [DecidableLT α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] : IteratorLoop (Rxo.Iterator α) Id n :=
  letI := openFinite (α := α)
  finiteRxoLoop

@[instance_reducible] public noncomputable def Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    ForIn' m (Rcc α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxc.Iterator α) Id m := finiteRxcLoop
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Rcc.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Rcc.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α] [LE α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    ForIn' m (Rco α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxo.Iterator α) Id m := finiteRxoLoop
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Rco.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Rco.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Rci.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    ForIn' m (Rci α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxi.Iterator α) Id m := finiteRxiLoop
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Rci.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Rci.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Roc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LT α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    ForIn' m (Roc α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxc.Iterator α) Id m := finiteRxcLoop
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Roc.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Roc.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Roo.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    ForIn' m (Roo α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxo.Iterator α) Id m := finiteRxoLoop
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Roo.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Roo.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Roi.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LT α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    ForIn' m (Roi α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxi.Iterator α) Id m := finiteRxiLoop
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Roi.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Roi.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [Least? α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    ForIn' m (Ric α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxc.Iterator α) Id m := finiteRxcLoop
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Ric.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Ric.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Rio.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LT α] [DecidableLT α] [Least? α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    ForIn' m (Rio α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxo.Iterator α) Id m := finiteRxoLoop
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Rio.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Rio.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

@[instance_reducible] public noncomputable def Std.Rii.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId {m} [UpwardEnumerable α] [Least? α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    ForIn' m (Rii α) α inferInstance where
  forIn' r init f := by
    letI : IteratorLoop (Rxi.Iterator α) Id m := finiteRxiLoop
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (α := α) (_root_.Std.Rii.Internal.iter r) init (fun a ha acc => f a ?_ acc)
    exact _root_.Std.Rii.Internal.isPlausibleIndirectOutput_iter_iff.mp ha

end OmegaChecks.InitPort.Alternatives
