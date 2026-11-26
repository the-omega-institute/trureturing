module

public import Init.Data.Range.Polymorphic.Iterators

/-! Finite consumers have a well-founded relation in their own interface. -/

open Std Std.PRange Std.Iterators

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
