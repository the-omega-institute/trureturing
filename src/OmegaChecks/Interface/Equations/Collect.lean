module
public import OmegaChecks.Interface.Equations.RangeLoop
import all Init.Data.Iterators.Consumers.Access

public import OmegaChecks.InitPort.Alternatives.Collect
import all OmegaChecks.InitPort.Alternatives.Collect
import all OmegaChecks.InitPort.Alternatives.Collect.Steps
import all OmegaChecks.InitPort.Alternatives.IteratorSlice
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
public import OmegaChecks.InitPort.Alternatives.Range
import all OmegaChecks.InitPort.Alternatives.Range
import all OmegaChecks.InitPort.Alternatives.Range.Characters
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.Data.Iterators.Producers.Monadic.List
import all Init.Data.Slice.Array.Iterator
import all Init.Data.Slice.List.Iterator
import all Init.Data.Iterators.Consumers.Monadic.Collect
import all Init.Data.Iterators.Combinators.Monadic.Take

/-! The finite collectors run the same step function as the general official collectors. -/

open Std Std.Iterators Std.Iterators.Types
namespace OmegaChecks.Interface.Equations

public theorem Std.IterM.Total.toArray {α : Type u} {m : Type u → Type v} {β : Type u}
    [Monad m] [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toArray it = it.toArray := by
  unfold OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toArray OmegaChecks.InitPort.Alternatives.collectArrayFrom
    _root_.Std.IterM.Total.toArray IterM.toArray IterM.toArray.go
  rw [WellFounded.extrinsicFix₂_eq_fix (OmegaChecks.InitPort.Alternatives.collectorWF (σ := Array β))]
  congr 1
  funext p recur
  congr 1
  funext step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

public theorem Std.IterM.Total.toListRev {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toListRev it = it.toListRev := by
  unfold OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toListRev OmegaChecks.InitPort.Alternatives.collectRevFrom
    _root_.Std.IterM.Total.toListRev IterM.toListRev IterM.toListRev.go
  rw [WellFounded.extrinsicFix₂_eq_fix (OmegaChecks.InitPort.Alternatives.collectorWF (σ := List β))]
  congr 1
  funext p recur
  congr 1
  funext step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

public theorem Std.Iterators.Types.Take.Rel {α β : Type w} (m : Type w → Type v)
    [Monad m] [Iterator α m β] [Productive α m] (a b : IterM (α := Take α m) m β) :
    OmegaChecks.InitPort.Alternatives.Std.Iterators.Types.Take.Rel m a b = _root_.Std.Iterators.Types.Take.Rel m a b := by
  apply propext
  unfold OmegaChecks.InitPort.Alternatives.Std.Iterators.Types.Take.Rel _root_.Std.Iterators.Types.Take.Rel
  split
  next hf =>
    rw [InvImage, Prod.lex_def]
    constructor
    · rintro (hlt | ⟨heq, hp | ⟨_, hfin⟩⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, .of_productive hp⟩
      · exact Or.inr ⟨heq, hfin⟩
    · rintro (hlt | ⟨heq, hfin⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, Or.inr ⟨hf, hfin⟩⟩
  next hnf =>
    rw [InvImage, Prod.lex_def]
    constructor
    · rintro (hlt | ⟨heq, hp | ⟨hf, _⟩⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, hp⟩
      · exact False.elim (hnf hf)
    · rintro (hlt | ⟨heq, hp⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, Or.inl hp⟩

public theorem instSliceSizeListSliceData (α : Type u) :
    @OmegaChecks.InitPort.Alternatives.instSliceSizeListSliceData α = @_root_.instSliceSizeListSliceData α := by
  change Std.Slice.SliceSize.mk _ = Std.Slice.SliceSize.mk _
  congr 1
  funext s
  change (match s.internalRepresentation.stop with
    | none => s.internalRepresentation.list.length
    | some n => min n s.internalRepresentation.list.length) = s.size
  rw [ListSlice.size_eq_length_toList, ListSlice.toList_eq]
  cases s.internalRepresentation.stop <;> simp [List.length_take]

public theorem Array.instAppendSubarray {α : Type u} :
    @OmegaChecks.InitPort.Alternatives.Array.instAppendSubarray α = @_root_.Array.instAppendSubarray α := by
  change Append.mk _ = Append.mk _
  congr 1

public theorem List.instAppendListSlice {α : Type u} :
    @OmegaChecks.InitPort.Alternatives.List.instAppendListSlice α = @_root_.List.instAppendListSlice α := by
  change Append.mk _ = Append.mk _
  congr 1
  funext x y
  change ((OmegaChecks.InitPort.Alternatives.listSliceContents x ++ OmegaChecks.InitPort.Alternatives.listSliceContents y).toSlice 0 _) =
    (x.toList ++ y.toList).toSlice 0 _
  rw [ListSlice.toList_eq (xs := x), ListSlice.toList_eq (xs := y)]
  rcases x with ⟨⟨a, o⟩⟩
  rcases y with ⟨⟨b, p⟩⟩
  cases o <;> cases p <;> rfl

private theorem contents_eq {α : Type u} (s : ListSlice α) :
    OmegaChecks.InitPort.Alternatives.listSliceContents s = s.toList := by
  rw [ListSlice.toList_eq]
  cases h : s.internalRepresentation.stop <;> simp [OmegaChecks.InitPort.Alternatives.listSliceContents, h]

public theorem Array.Subarray.repr {α : Type u} [Repr α] (s : Subarray α) :
    OmegaChecks.InitPort.Alternatives.Array.Subarray.repr s = _root_.Array.Subarray.repr s := by
  unfold OmegaChecks.InitPort.Alternatives.Array.Subarray.repr _root_.Array.Subarray.repr
  exact congrArg (fun a : Array α => _root_.repr a ++ ".toSubarray") Subarray.copy_eq_toArray

public theorem Array.instToStringSubarray {α : Type u} [ToString α] :
    @OmegaChecks.InitPort.Alternatives.Array.instToStringSubarray α _ = @_root_.Array.instToStringSubarray α _ := by
  change ToString.mk _ = ToString.mk _
  congr 1

public theorem List.ListSlice.repr {α : Type u} [Repr α] (s : ListSlice α) :
    OmegaChecks.InitPort.Alternatives.List.ListSlice.repr s = _root_.List.ListSlice.repr s := by
  unfold OmegaChecks.InitPort.Alternatives.List.ListSlice.repr _root_.List.ListSlice.repr
  rw [contents_eq]

public theorem List.instToStringListSlice {α : Type u} [ToString α] :
    @OmegaChecks.InitPort.Alternatives.List.instToStringListSlice α _ = @_root_.List.instToStringListSlice α _ := by
  change ToString.mk _ = ToString.mk _
  congr 1
  funext s
  change toString (OmegaChecks.InitPort.Alternatives.listSliceContents s).toArray = toString s.toArray
  rw [contents_eq, ListSlice.toArray_toList]

private theorem finiteIteratorLoop_eq {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type x → Type x'} [Monad n] :
    OmegaChecks.InitPort.Alternatives.finiteIteratorLoop (α := α) (m := m) (n := n) =
      IteratorLoop.defaultImplementation := by
  change IteratorLoop.mk _ = IteratorLoop.mk _
  congr 1
  funext lift γ Pl it init f
  letI : Nonempty γ := ⟨init⟩
  unfold OmegaChecks.InitPort.Alternatives.finiteForIn IterM.DefaultConsumers.forIn'
  rw [WellFounded.extrinsicFix₃_eq_fix (InvImage.wf _ (IteratorLoop.wellFounded_of_finite (P := Pl)))]
  dsimp only
  congr 1
  funext p recur
  congr 1
  funext step
  cases step.inflate using PlausibleIterStep.casesOn with
  | yield next out plausible =>
    dsimp only
    congr 1
    funext result
    rcases result with ⟨result, h⟩
    cases result <;> rfl
  | skip => rfl
  | done => rfl

public theorem instIteratorLoopSubarrayIteratorIdOfMonad {α : Type u} {m : Type v → Type w} [Monad m] :
    @OmegaChecks.InitPort.Alternatives.instIteratorLoopSubarrayIteratorIdOfMonad α m _ =
      @_root_.instIteratorLoopSubarrayIteratorIdOfMonad α m _ :=
  finiteIteratorLoop_eq

public theorem Std.Iterators.Types.ListIterator.instIteratorLoop {m : Type w → Type w'} {α : Type w}
    [Monad m] {n : Type x → Type x'} [Monad n] :
    @OmegaChecks.InitPort.Alternatives.Std.Iterators.Types.ListIterator.instIteratorLoop m α _ n _ =
      @_root_.Std.Iterators.Types.ListIterator.instIteratorLoop m α _ n _ :=
  finiteIteratorLoop_eq

public theorem instForInListSliceOfMonad.{v,w,u} {α : Type u} {m : Type v → Type w} [Monad m] :
    @OmegaChecks.InitPort.Alternatives.instForInListSliceOfMonad α m _ =
      @_root_.instForInListSliceOfMonad α m _ := by
  unfold OmegaChecks.InitPort.Alternatives.instForInListSliceOfMonad _root_.instForInListSliceOfMonad
  congr 1
  funext β xs init f
  rw [finiteIteratorLoop_eq]

public theorem Std.Iter.Total.atIdxSlow? {α β : Type u} [Iterator α Id β] [Productive α Id]
    (n : Nat) (it : Iter.Total (α := α) β) :
    OmegaChecks.InitPort.Alternatives.Std.Iter.Total.atIdxSlow? n it = it.atIdxSlow? n := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Iter.Total.atIdxSlow? _root_.Std.Iter.Total.atIdxSlow? Iter.atIdxSlow?
  rw [WellFounded.extrinsicFix₂_eq_fix (OmegaChecks.InitPort.Alternatives.indexWF (α := α) (β := β))]
  congr 1
  funext p recur
  rcases p with ⟨i, k⟩
  cases i.step using PlausibleIterStep.casesOn <;> cases k <;> rfl

end OmegaChecks.Interface.Equations
