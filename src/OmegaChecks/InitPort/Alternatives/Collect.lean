module

public import OmegaChecks.InitPort.Alternatives.Collect.Range
public import OmegaChecks.InitPort.Alternatives.Collect.Steps

public import Init.Data.Iterators.Lemmas.Producers.Monadic.List
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Iterators.Combinators.Monadic.Take
public import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Iterators.Lemmas.Combinators.Attach
import all Init.Data.Iterators.Combinators.Monadic.Attach
import Init.Data.Iterators.Lemmas.Combinators.Monadic.Attach
public import Init.Data.Iterators.Lemmas.Combinators.ULift
public import Init.Data.Iterators.Lemmas.Combinators.Append
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import all Init.Data.Iterators.Lemmas.Combinators.FilterMap
import all Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
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

section IndexCombinators

attribute [local simp] PlausibleIterStep.yield PlausibleIterStep.skip PlausibleIterStep.done

local macro "getAt" it:term:max n:term:max : term =>
  `(Std.Iter.Total.atIdxSlow? $n (Iter.ensureTermination $it))

public theorem Std.Iter.atIdxSlow?_appendSnd {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Productive α₁ Id] [Productive α₂ Id]
    {it₂ : Iter (α := α₂) β} {n : Nat} :
    getAt (Iter.Intermediate.appendSnd α₁ it₂) n = getAt it₂ n := by
  induction n, it₂ using Std.Iter.atIdxSlow?.induct_unfolding with
  | yield_zero it it' out h h' =>
    simp only [Std.Iter.atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Iter.Intermediate.step_appendSnd, h']
    rfl
  | yield_succ it it' out h h' n ih =>
    simp only [Std.Iter.atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Iter.Intermediate.step_appendSnd, h']
    exact ih
  | skip_case n it it' h h' ih =>
    simp only [Std.Iter.atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Iter.Intermediate.step_appendSnd, h']
    exact ih
  | done_case n it h h' =>
    simp only [Std.Iter.atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Iter.Intermediate.step_appendSnd, h']
    rfl

public theorem Std.Iter.atIdxSlow?_append_of_eq_some {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} {n : Nat} {b : β}
    (h : getAt it₁ n = some b) :
    getAt (it₁.append it₂) n = some b := by
  induction n, it₁ using Std.Iter.atIdxSlow?.induct_unfolding generalizing it₂ with
  | yield_zero it it' out hp h' =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂)]
    cases h
    simp [Iter.step_append, h'] <;> rfl
  | yield_succ it it' out hp h' n ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂)]
    simp [Iter.step_append, h', ih h]
  | skip_case n it it' hp h' ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂)]
    simp [Iter.step_append, h', ih h]
  | done_case n it hp h' =>
    cases h

public theorem Std.Iter.atIdxSlow?_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} {n : Nat} :
    getAt (it₁.append it₂) n =
      if n < (Std.Iter.Total.toList it₁.ensureTermination).length then getAt it₁ n
      else getAt it₂ (n - (Std.Iter.Total.toList it₁.ensureTermination).length) := by
  induction n, it₁ using Std.Iter.atIdxSlow?.induct_unfolding generalizing it₂ with
  | yield_zero it it' out h hs =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂), Iter.step_append, hs,
      Std.Iter.toList_eq_match_step (it := it), hs]
    exact (if_pos (Nat.zero_lt_succ _)).symm
  | yield_succ it it' out h hs n ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂), Iter.step_append, hs,
      Std.Iter.toList_eq_match_step (it := it), hs]
    let len := (Std.Iter.Total.toList it'.ensureTermination).length
    change getAt (it'.append it₂) n = if n.succ < len.succ then getAt it' n else getAt it₂ (n.succ - len.succ)
    rw [ih (it₂ := it₂), Nat.succ_sub_succ]
    by_cases hn : n < len
    · rw [if_pos hn, if_pos (Nat.succ_lt_succ hn)]
    · rw [if_neg hn, if_neg (fun h => hn (Nat.lt_of_succ_lt_succ h))]
  | skip_case n it it' h hs ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂), Iter.step_append, hs,
      Std.Iter.toList_eq_match_step (it := it), hs]
    exact ih
  | done_case n it h hs =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂), Iter.step_append, hs,
      Std.Iter.toList_eq_match_step (it := it), hs]
    change getAt (Iter.Intermediate.appendSnd α₁ it₂) n = if n < 0 then none else getAt it₂ (n - 0)
    rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero]
    exact Std.Iter.atIdxSlow?_appendSnd

public theorem Std.Iter.atIdxSlow?_append_of_productive {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} {n k : Nat}
    (hk : getAt it₁ k = none)
    (hmin : ∀ j, j < k → (getAt it₁ j).isSome)
    (hle : k ≤ n) :
    getAt (it₁.append it₂) n = getAt it₂ (n - k) := by
  induction n, it₁ using Std.Iter.atIdxSlow?.induct_unfolding generalizing k it₂ with
  | yield_zero it it' out hp h' =>
    exfalso
    have : k = 0 := Nat.eq_zero_of_le_zero hle
    subst this
    rw [Std.Iter.atIdxSlow?_eq_match (it := it)] at hk
    rw [h'] at hk
    cases hk
  | yield_succ it it' out hp h' n ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂)]
    rw [Iter.step_append, h']
    match k with
    | 0 =>
      rw [Std.Iter.atIdxSlow?_eq_match (it := it)] at hk
      rw [h'] at hk
      cases hk
    | k + 1 =>
      rw [Std.Iter.atIdxSlow?_eq_match (it := it)] at hk
      rw [h'] at hk
      have hmin' : ∀ j, j < k → (getAt it' j).isSome := by
        intro j hj
        have h := hmin (j + 1) (by omega)
        rw [Std.Iter.atIdxSlow?_eq_match (it := it)] at h
        rw [h'] at h
        exact h
      change getAt (it'.append it₂) n = getAt it₂ (n.succ - (k + 1))
      rw [Nat.succ_sub_succ]
      exact (ih (it₂ := it₂) hk hmin' (Nat.le_of_succ_le_succ hle))
  | skip_case n it it' hp h' ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂)]
    rw [Iter.step_append, h']
    rw [Std.Iter.atIdxSlow?_eq_match (it := it), h'] at hk
    have hmin' : ∀ j, j < k → (getAt it' j).isSome := by
      intro j hj
      have h := hmin j hj
      rw [Std.Iter.atIdxSlow?_eq_match (it := it)] at h
      rw [h'] at h
      exact h
    exact ih hk hmin' hle
  | done_case n it hp h' =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.append it₂)]
    rw [Iter.step_append, h']
    have hk0 : k = 0 := by
      cases k with
      | zero => rfl
      | succ k =>
        have h := hmin 0 (Nat.zero_lt_succ k)
        rw [Std.Iter.atIdxSlow?_eq_match (it := it), h'] at h
        cases h
    change getAt (Iter.Intermediate.appendSnd α₁ it₂) n = getAt it₂ (n - k)
    rw [hk0, Nat.sub_zero]
    exact (Std.Iter.atIdxSlow?_appendSnd (α₁ := α₁) (it₂ := it₂) (n := n))

public theorem Std.Iter.atIdxSlow?_take {α β}
    [Iterator α Id β] [Productive α Id] {k l : Nat}
    {it : Iter (α := α) β} :
    getAt (it.take k) l = if l < k then getAt it l else none := by
  induction l, it using Std.Iter.atIdxSlow?.induct_unfolding generalizing k
  case yield_zero it next out h hs =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.take k), Iter.step_take]
    cases k with
    | zero => rfl
    | succ k =>
      rw [hs]
      exact (if_pos (Nat.zero_lt_succ k)).symm
  case yield_succ it next out h hs l ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.take k), Iter.step_take]
    cases k with
    | zero => rfl
    | succ k =>
      rw [hs]
      change getAt (next.take k) l = if l.succ < k.succ then getAt next l else none
      rw [ih]
      by_cases hl : l < k
      · rw [if_pos hl, if_pos (Nat.succ_lt_succ hl)]
      · rw [if_neg hl, if_neg (fun h => hl (Nat.lt_of_succ_lt_succ h))]
  case skip_case l it next h hs ih =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.take k), Iter.step_take]
    cases k with
    | zero => rw [if_neg (Nat.not_lt_zero l)]; rfl
    | succ k => rw [hs]; exact ih
  case done_case l it h hs =>
    rw [Std.Iter.atIdxSlow?_eq_match (it := it.take k), Iter.step_take]
    cases k with
    | zero => rw [if_neg (Nat.not_lt_zero l)]; rfl
    | succ k =>
      rw [hs]
      by_cases hl : l < k.succ
      · rw [if_pos hl]; rfl
      · rw [if_neg hl]; rfl

public theorem Std.Iter.toList_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    Std.Iter.Total.toList (it₁.append it₂).ensureTermination =
      Std.Iter.Total.toList it₁.ensureTermination ++ Std.Iter.Total.toList it₂.ensureTermination := by
  apply List.ext_getElem?
  intro k
  rw [Std.Iter.getElem?_toList_eq_atIdxSlow?, Std.Iter.atIdxSlow?_append, List.getElem?_append,
    Std.Iter.getElem?_toList_eq_atIdxSlow?, Std.Iter.getElem?_toList_eq_atIdxSlow?]

public theorem Std.Iter.toListRev_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    (Std.IterM.Total.toListRev (it₁.append it₂).toIterM.ensureTermination).run =
      (Std.IterM.Total.toListRev it₂.toIterM.ensureTermination).run ++ (Std.IterM.Total.toListRev it₁.toIterM.ensureTermination).run := by
  rw [Std.Iter.toListRev_eq (it := it₁.append it₂), Std.Iter.toListRev_eq (it := it₂), Std.Iter.toListRev_eq (it := it₁)]
  exact (congrArg List.reverse (Std.Iter.toList_append (it₁ := it₁) (it₂ := it₂))).trans List.reverse_append

public theorem Std.Iter.toArray_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    (Std.IterM.Total.toArray (it₁.append it₂).toIterM.ensureTermination).run =
      (Std.IterM.Total.toArray it₁.toIterM.ensureTermination).run ++ (Std.IterM.Total.toArray it₂.toIterM.ensureTermination).run := by
  apply Array.ext'
  rw [Array.toList_append]
  exact Std.Iter.toList_append (it₁ := it₁) (it₂ := it₂)

end IndexCombinators

private theorem arrayFromList {β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (xs : List β) (acc : Array β) :
    collectArrayFrom (xs.iterM m) acc = pure (acc ++ xs.toArray) := by
  induction xs generalizing acc with
  | nil =>
    unfold collectArrayFrom
    rw [WellFounded.fix_eq]
    dsimp only
    rw [List.step_iterM_nil, pure_bind, Shrink.inflate_deflate]
    rw [Array.append_empty]
  | cons x xs ih =>
    conv => lhs; unfold collectArrayFrom; rw [WellFounded.fix_eq]
    dsimp only
    rw [List.step_iterM_cons, pure_bind, Shrink.inflate_deflate]
    change collectArrayFrom (xs.iterM m) (acc.push x) = _
    rw [ih]
    apply congrArg pure
    apply Array.ext'
    rw [Array.toList_append, Array.toList_append, Array.toList_push, List.toList_toArray,
      List.toList_toArray, List.append_assoc]
    rfl

public theorem List.toArray_iterM {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w} {l : List β} :
    Std.IterM.Total.toArray (l.iterM m).ensureTermination = pure l.toArray := by
  change collectArrayFrom (l.iterM m) #[] = _
  rw [arrayFromList, Array.empty_append]

public theorem List.toList_iterM {m : Type w → Type w'} [Monad m] {β : Type w} [LawfulMonad m] {l : List β} :
    Std.IterM.Total.toList (l.iterM m).ensureTermination = pure l := by
  unfold Std.IterM.Total.toList
  rw [List.toArray_iterM, map_pure, List.toList_toArray]

private theorem reverseFromList {β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (xs : List β) (acc : List β) :
    collectRevFrom (xs.iterM m) acc = pure (xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil =>
    unfold collectRevFrom
    rw [WellFounded.fix_eq]
    dsimp only
    rw [List.step_iterM_nil, pure_bind, Shrink.inflate_deflate]
    rfl
  | cons x xs ih =>
    conv => lhs; unfold collectRevFrom; rw [WellFounded.fix_eq]
    dsimp only
    rw [List.step_iterM_cons, pure_bind, Shrink.inflate_deflate]
    change collectRevFrom (xs.iterM m) (x :: acc) = _
    rw [ih, List.reverse_cons, List.append_assoc]
    rfl

public theorem List.toListRev_iterM {m : Type w → Type w'} [Monad m] {β : Type w} [LawfulMonad m] {l : List β} :
    Std.IterM.Total.toListRev (l.iterM m).ensureTermination = pure l.reverse := by
  change collectRevFrom (l.iterM m) [] = _
  rw [reverseFromList, List.append_nil]

public theorem Std.Iter.toList_uLift {α β : Type u} [Iterator α Id β] {it : Iter (α := α) β} [Finite α Id] :
    Std.Iter.Total.toList it.uLift.ensureTermination = (Std.Iter.Total.toList it.ensureTermination).map ULift.up := by
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [Std.Iter.toList_eq_match_step (it := it.uLift), Std.Iter.toList_eq_match_step (it := it), Std.Iter.step_uLift]
    cases it.step using PlausibleIterStep.casesOn with
    | yield next out h => exact congrArg (List.cons (ULift.up out)) (ihy h)
    | skip next h => exact ihs h
    | done h => rfl

public theorem Std.Iter.length_uLift : type_of% @_root_.Std.Iter.length_uLift := by
  intros
  rw [← _root_.Std.Iter.length_toList_eq_length, ← _root_.Std.Iter.length_toList_eq_length,
    _root_.Std.Iter.toList_uLift, List.length_map]

private theorem collectAttach {α β : Type w} [Iterator α Id β] [Finite α Id] {P : β → Prop}
    (it : IterM (α := α) Id β) (hP : ∀ out, it.IsPlausibleIndirectOutput out → P out) :
    (collectInto (it.attachWith P hP) #[]).toList.unattach = (collectInto it #[]).toList := by
  induction it using (Finite.wf (α := α) (m := Id) (β := β)).induction with
  | h it ih =>
    rw [collectList_eq (it.attachWith P hP), collectList_eq it, IterM.step_attachWith]
    dsimp only [Functor.map, Id.run]
    rw [Shrink.inflate_deflate]
    cases it.step.inflate using PlausibleIterStep.casesOn with
    | yield next out h =>
      exact congrArg (List.cons out) (ih next ⟨_, rfl, h⟩ (fun x hx => hP x (.indirect ⟨_, rfl, h⟩ hx)))
    | skip next h =>
      exact ih next ⟨_, rfl, h⟩ (fun x hx => hP x (.indirect ⟨_, rfl, h⟩ hx))
    | done h => rfl

public theorem Std.Iter.unattach_toList_attachWith {α β : Type w} {P : β → Prop} [Iterator α Id β]
    {it : Iter (α := α) β} {hP} [Finite α Id] :
    (Std.Iter.Total.toList (it.attachWith P hP).ensureTermination).unattach =
      Std.Iter.Total.toList it.ensureTermination := by
  exact collectAttach it.toIterM (fun out h => hP out (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h))

section FlatMapOutput

local macro "outputs[" it:term "]" : term => `(Std.Iter.Total.toList (Iter.ensureTermination $it))

private theorem innerOutputs {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id] (f : β → Iter (α := α₂) γ) (outer : Iter (α := α) β)
    (inner : Iter (α := α₂) γ) :
    outputs[outer.flatMapAfter f (some inner)] = outputs[inner] ++ outputs[outer.flatMapAfter f none] := by
  induction inner using _root_.Std.Iter.inductSteps with
  | step i ihy ihs =>
    rw [Std.Iter.toList_eq_match_step (it := outer.flatMapAfter f (some i)),
      Std.Iter.toList_eq_match_step (it := i), Std.Iter.step_flatMapAfter]
    dsimp only
    cases i.step using PlausibleIterStep.casesOn with
    | yield next out h => exact congrArg (List.cons out) (ihy h)
    | skip next h => exact ihs h
    | done h => rfl

public theorem Std.Iter.toList_flatMapAfter {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id] {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β}
    {it₂ : Option (Iter (α := α₂) γ)} :
    outputs[it₁.flatMapAfter f it₂] = Option.casesOn it₂
      outputs[it₁.map fun b => outputs[f b]].flatten
      (fun inner => outputs[inner] ++ outputs[it₁.map fun b => outputs[f b]].flatten) := by
  have emptyInner (it : Iter (α := α) β) :
      outputs[it.flatMapAfter f none] = outputs[it.map fun b => outputs[f b]].flatten := by
    induction it using _root_.Std.Iter.inductSteps with
    | step i ihy ihs =>
      rw [Std.Iter.toList_eq_match_step (it := i.flatMapAfter f none), Std.Iter.step_flatMapAfter,
        Std.Iter.toList_eq_match_step (it := i.map _), Std.Iter.step_map]
      cases i.step using PlausibleIterStep.casesOn with
      | yield next out h =>
        exact (innerOutputs f next (f out)).trans (congrArg (outputs[f out] ++ ·) (ihy h))
      | skip next h => exact ihs h
      | done h => rfl
  cases it₂ with
  | none => exact emptyInner it₁
  | some inner => exact (innerOutputs f it₁ inner).trans (congrArg (outputs[inner] ++ ·) (emptyInner it₁))

local macro "arrayOutputs[" it:term "]" : term => `((Std.IterM.Total.toArray (IterM.ensureTermination (Iter.toIterM $it))).run)

public theorem Std.Iter.toList_flatMap {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id] [Iterator α Id β] [Iterator α₂ Id γ] [Finite α Id] [Finite α₂ Id]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} :
    outputs[it₁.flatMap f] = outputs[it₁.map fun b => outputs[f b]].flatten :=
  Std.Iter.toList_flatMapAfter (f := f) (it₁ := it₁) (it₂ := none)

private theorem mappedArrays {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id] (f : β → Iter (α := α₂) γ) (it : Iter (α := α) β) :
    outputs[it.map fun b => outputs[f b]] = outputs[it.map fun b => arrayOutputs[f b]].map Array.toList := by
  induction it using _root_.Std.Iter.inductSteps with
  | step i ihy ihs =>
    rw [Std.Iter.toList_eq_match_step (it := i.map fun b => outputs[f b]), Std.Iter.step_map,
      Std.Iter.toList_eq_match_step (it := i.map fun b => arrayOutputs[f b]), Std.Iter.step_map]
    cases i.step using PlausibleIterStep.casesOn with
    | yield next out h => exact congrArg (List.cons outputs[f out]) (ihy h)
    | skip next h => exact ihs h
    | done h => rfl

public theorem Std.Iter.toArray_flatMapAfter {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id] {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} {it₂ : Option (Iter (α := α₂) γ)} :
    arrayOutputs[it₁.flatMapAfter f it₂] = Option.casesOn it₂
      arrayOutputs[it₁.map fun b => arrayOutputs[f b]].flatten
      (fun inner => arrayOutputs[inner] ++ arrayOutputs[it₁.map fun b => arrayOutputs[f b]].flatten) := by
  apply Array.ext'
  cases it₂ with
  | none =>
    change outputs[it₁.flatMapAfter f none] = (arrayOutputs[it₁.map fun b => arrayOutputs[f b]].flatten).toList
    rw [Std.Iter.toList_flatMapAfter, Array.toList_flatten]
    exact congrArg List.flatten (mappedArrays f it₁)
  | some inner =>
    change outputs[it₁.flatMapAfter f (some inner)] =
      (arrayOutputs[inner] ++ arrayOutputs[it₁.map fun b => arrayOutputs[f b]].flatten).toList
    rw [Std.Iter.toList_flatMapAfter, Array.toList_append, Array.toList_flatten]
    exact congrArg (fun x => outputs[inner] ++ List.flatten x) (mappedArrays f it₁)

public theorem Std.Iter.toArray_flatMap {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id] [Iterator α Id β] [Iterator α₂ Id γ] [Finite α Id] [Finite α₂ Id]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} :
    arrayOutputs[it₁.flatMap f] = arrayOutputs[it₁.map fun b => arrayOutputs[f b]].flatten :=
  Std.Iter.toArray_flatMapAfter (f := f) (it₁ := it₁) (it₂ := none)

end FlatMapOutput

public theorem Std.IterM.toList_take_zero {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite (Take α m) m] {it : IterM (α := α) m β} :
    Std.IterM.Total.toList (it.take 0).ensureTermination = pure [] := by
  have stop : (it.take 0).step = pure (.deflate ⟨.done, Take.PlausibleStep.depleted rfl⟩) := rfl
  change Array.toList <$> collectArrayFrom (it.take 0) #[] = _
  unfold collectArrayFrom
  rw [WellFounded.fix_eq]
  dsimp only
  rw [stop, pure_bind, Shrink.inflate_deflate]
  change Array.toList <$> (pure (#[] : Array β) : m (Array β)) = pure []
  rw [map_pure]

end OmegaChecks.InitPort.Alternatives
