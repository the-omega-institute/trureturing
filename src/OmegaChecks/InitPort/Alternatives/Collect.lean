module

public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Iterators.Combinators.Monadic.Take

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
